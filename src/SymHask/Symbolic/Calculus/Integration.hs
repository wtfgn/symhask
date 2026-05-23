{-# LANGUAGE ViewPatterns #-}

-- |
-- Module: SymHask.Symbolic.Calculus.Integration
-- Description: Symbolic integration of expressions
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
--
-- Integration of symbolic expressions with respect to variables,
-- including support for common functions and an integration table for pattern matching.
module SymHask.Symbolic.Calculus.Integration
    ( -- * Algorithms
      integrate
    , integrateLinear
    , integrateTable
      -- * Substitution method
    , trialSubstitutions
    ) where

import           Control.Applicative                       ((<|>))
import           Data.Either.Extra                         (eitherToMaybe)
import qualified Data.HashSet                              as HS
import           Data.List                                 (find, sortOn)
import           Data.List.NonEmpty                        (NonEmpty ((:|)))
import qualified Data.List.NonEmpty                        as NE
import           Data.Text                                 (Text)
import           SymHask.Printer
import           SymHask.Symbolic
import           SymHask.Symbolic.Basic                    (Pattern (..),
                                                            Replacement (..),
                                                            completeSubExprs,
                                                            freeOf,
                                                            separateFactors,
                                                            subs, treeSize)
import           SymHask.Symbolic.Calculus.Differentiation (diff, mkDiffVar)
import           SymHask.Symbolic.Polynomial               (algebraicExpand)
import           SymHask.Symbolic.Simplification           ((.**.), (.*.),
                                                            (./.))
-- ============================================================================

-- * Data Types

-- ============================================================================

-- | Rule in the integration table
data IntegrationRule
  = IntegrationRule
      { ruleName           :: Text
        -- Description of the rule
      , ruleMatcher        :: Text -> SimplifiedExpr -> Bool
        -- Does this rule match?
      , ruleAntiderivative :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
        -- Apply the rule to get antiderivative (or Nothing if application fails)
      }

-- ============================================================================

-- * Helpers

-- ============================================================================


-- | Check if an expression is free of the integration variable
isFreeOf :: Text -> SimplifiedExpr -> Bool
isFreeOf s expr = freeOf expr (mkSymbol s)

-- isFreeOf (IntFunction fname args) expr =
--   let funcExpr = TextToExpr (IntFunction fname args)
--   in freeOf expr funcExpr

-- ============================================================================

-- * Category Matchers

-- ============================================================================

{- | Category 1: Constants (free of integration variable)
∫ c dx = c*x
-}
matchConstant :: Text -> SimplifiedExpr -> Bool
matchConstant = isFreeOf

-- This computes:
integrateConstant :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateConstant x c = eitherToMaybe (c .*. mkSymbol x)

-- integrateConstant (IntFunction fname args) c =
--   let var = TextToExpr (IntFunction fname args)
--   in Just $ c .*. var

{- | Category 2a: Power rule for x^n where n != -1
∫ x^n dx = x^(n+1) / (n+1) where n is free of x
-}
matchPowerGeneral :: Text -> SimplifiedExpr -> Bool
matchPowerGeneral var expr = case expr of
  -- handle implicit exponent 1: Symbol 'x' treated as x^1
  Symbol' s | s ==  var                                                 -> True
  Power' (Symbol' s) n | s ==  var && isFreeOf var n && isNotMinusOne n -> True
  _                                                                     -> False
 where
  isNotMinusOne (Number' (-1)) = False
  isNotMinusOne _              = True

integratePowerGeneral :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integratePowerGeneral _ expr = case expr of
  -- Symbol x -> treat as x^1
  Symbol' s ->
    let x = mkSymbol s :: UnsimplifiedExpr
     in eitherToMaybe $ simplify ((x ** 2) / 2)
  Power' x n -> do
    -- ∫ x^n dx = x^(n+1) / (n+1)
    nPlusOne <- case n of
      Number' k -> Just $ mkNumber (k + 1)
      _         -> Nothing -- Handle non-numeric exponents later
    xPowerNPlus1 <- eitherToMaybe (x .**. nPlusOne)
    let denominator = nPlusOne
    eitherToMaybe (xPowerNPlus1 ./. denominator)
  _ -> Nothing

{- | Category 2b: Logarithm for x^(-1)
∫ x^(-1) dx = ln(x)
-}
matchPowerLog ::  Text -> SimplifiedExpr  -> Bool
matchPowerLog var expr = case expr of
  Power' (Symbol' s) (Number' (-1)) | s ==  var -> True
  Quotient' (Number' 1) (Symbol' s) | s ==  var -> True
  _                                             -> False

integratePowerLog :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integratePowerLog x _ = Just $ mkFunction "log" (mkSymbol x :| [])

-- integratePowerLog (IntFunction fname args) _ =
--   let funcExpr = TextToExpr (IntFunction fname args)
--   in Just $ mkFunction "log" (funcExpr :| [])

{- | Category 3a: Exponential e^x
∫ e^x dx = e^x
-}
matchExpX :: Text ->SimplifiedExpr -> Bool
matchExpX var expr  = case expr of
  Exp' (Symbol' s) | s ==  var -> True
  _                            -> False

integrateExpX :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateExpX _ (Exp' x) = Just $ mkFunction "exp" (x :| [])
integrateExpX _ _        = Nothing

{- | Category 3b: Natural logarithm ln(x)
∫ ln(x) dx = x*ln(x) - x
-}
matchLogX :: Text -> SimplifiedExpr -> Bool
matchLogX var expr = case expr of
  Log' (Symbol' s) | s ==  var -> True
  _                            -> False

integrateLogX :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateLogX x _ =
  let xSym = mkSymbol x :: UnsimplifiedExpr
      res = simplify $ (xSym * mkFunction "log" (xSym :| [])) - xSym
   in eitherToMaybe res

{- | Category 3c: General exponential b^x where b is free of x
∫ b^x dx = b^x / ln(b)
-}
matchExpBX :: Text -> SimplifiedExpr -> Bool
matchExpBX var expr = case expr of
  Power' b (Symbol' s) | isFreeOf var b  && s ==  var -> True
  _                                                   -> False


integrateExpBX :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateExpBX _ (Power' (unsimplify -> b) (unsimplify -> x)) =
  eitherToMaybe $ simplify $ (b ** x) / mkFunction "log" (b :| [])
integrateExpBX _ _ = Nothing

{- | Category 4a: sin(x)
∫ sin(x) dx = -cos(x)
-}
matchSinX :: Text -> SimplifiedExpr -> Bool
matchSinX var expr = case expr of
  Sin' (Symbol' s) | s ==  var -> True
  _                            -> False

integrateSinX :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateSinX _ (Sin' x) = eitherToMaybe $ simplify $ mkUnaryDiff (mkFunction "cos" (x :| []))
integrateSinX _ _ = Nothing

{- | Category 4b: cos(x)
∫ cos(x) dx = sin(x)
-}
matchCosX :: Text -> SimplifiedExpr -> Bool
matchCosX var expr = case expr of
  Cos' (Symbol' s) | s ==  var -> True
  _                            -> False

integrateCosX :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateCosX _ (Cos' x) = Just $ mkFunction "sin" (x :| [])
integrateCosX _ _        = Nothing

{- | Category 4c: tan(x)
∫ tan(x) dx = -ln(cos(x)) or ln(|sec(x)|), use -ln(cos(x))
-}
matchTanX :: Text -> SimplifiedExpr -> Bool
matchTanX var expr = case expr of
  Tan' (Symbol' s) | s ==  var -> True
  _                            -> False

integrateTanX :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateTanX _ (Tan' x) =
  eitherToMaybe $ simplify $ mkUnaryDiff (mkFunction "log" (mkFunction "cos" (x :| []) :| []))
integrateTanX _ _ = Nothing

{- | Category 4d: cot(x)
∫ cot(x) dx = ln(sin(x))
-}
matchCotX :: Text -> SimplifiedExpr -> Bool
matchCotX var expr = case expr of
  Cot' (Symbol' s) | s ==  var -> True
  _                            -> False

integrateCotX :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateCotX _ (Cot' x) = Just $ mkFunction "log" (mkFunction "sin" (x :| []) :| [])
integrateCotX _ _ = Nothing

{- | Category 4e: sec(x)
∫ sec(x) dx = ln(sec(x) + tan(x))
-}
matchSecX :: Text -> SimplifiedExpr -> Bool
matchSecX var expr = case expr of
  Sec' (Symbol' s) | s ==  var -> True
  _                            -> False

integrateSecX :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateSecX _ (Sec' (unsimplify -> x)) =
  let secX = mkFunction "sec" (x :| [])
      tanX = mkFunction "tan" (x :| [])
   in eitherToMaybe $ simplify $ mkFunction "log" ((secX + tanX) :| [])
integrateSecX _ _ = Nothing

{- | Category 4f: csc(x)
∫ csc(x) dx = -ln(csc(x) + cot(x))
-}
matchCscX :: Text -> SimplifiedExpr -> Bool
matchCscX var expr = case expr of
  Csc' (Symbol' s) | s ==  var -> True
  _                            -> False

integrateCscX :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateCscX _ (Csc' (unsimplify -> x)) =
  let cscX = mkFunction "csc" (x :| [])
      cotX = mkFunction "cot" (x :| [])
   in eitherToMaybe $ simplify $ mkUnaryDiff (mkFunction "log" ((cscX + cotX) :| []))
integrateCscX _ _ = Nothing

{- | Category 4g: sec^2(x)
∫ sec^2(x) dx = tan(x)
-}
matchSec2X :: Text -> SimplifiedExpr -> Bool
matchSec2X var expr = case expr of
  Power' (Sec' (Symbol' s)) (Number' 2) | s ==  var -> True
  _                                                 -> False

integrateSec2X :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateSec2X _ (Power' (Sec' x) _) = eitherToMaybe $ simplify $ mkFunction "tan" (x :| [])
integrateSec2X _ _ = Nothing

{- | Category 4h: csc^2(x)
∫ csc^2(x) dx = -cot(x)
-}
matchCsc2X :: Text -> SimplifiedExpr -> Bool
matchCsc2X var expr = case expr of
  Power' (Csc' (Symbol' s)) (Number' 2) | s ==  var -> True
  _                                                 -> False

integrateCsc2X :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateCsc2X _ (Power' (Csc' x) _) = eitherToMaybe $ simplify $ mkUnaryDiff (mkFunction "cot" (x :| []))
integrateCsc2X _ _ = Nothing

-- | Category 5: Special forms from derivatives of trig/inverse trig functions

{- | Category 5a: sec(x)*tan(x)
∫ sec(x)*tan(x) dx = sec(x)
-}
matchSecTanX :: Text -> SimplifiedExpr -> Bool
matchSecTanX var expr = case expr of
  Product' factors | check factors -> True
  _                                -> False
 where
  check = liftA2 (&&) hasSecX hasTanX
  hasSecX = any (\case Sec' (Symbol' s) | s ==  var -> True; _ -> False)
  hasTanX = any (\case Tan' (Symbol' s) | s ==  var -> True; _ -> False)


integrateSecTanX :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateSecTanX var (Product' factors) = do
  let secFactor = find (\case Sec' (Symbol' s) | s == var -> True; _ -> False) factors
  secFactor >>= \(Sec' x) -> Just $ mkFunction "sec" (x :| [])
integrateSecTanX _ _ = Nothing

{- | Category 5b: csc(x)*cot(x)
∫ csc(x)*cot(x) dx = -csc(x)
-}
matchCscCotX :: Text -> SimplifiedExpr -> Bool
matchCscCotX var expr = case expr of
  Product' factors | check factors -> True
  _                                -> False
 where
  check = liftA2 (&&) hasCscX hasCotX
  hasCscX = any (\case Csc' (Symbol' s) | s == var -> True; _ -> False)
  hasCotX = any (\case Cot' (Symbol' s) | s == var -> True; _ -> False)


integrateCscCotX :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateCscCotX var (Product' factors) = do
  let cscFactor = find (\case Csc' (Symbol' s) | s ==  var -> True; _ -> False) factors
  cscFactor >>= \(Csc' x) -> eitherToMaybe $ simplify $ mkUnaryDiff (mkFunction "csc" (x :| []))
integrateCscCotX _ _ = Nothing

-- ============================================================================

-- * Integration Table

-- ============================================================================

{- | The integration table, ordered by category and complexity
Simpler patterns are tried first to fail fast
-}
integrationTable :: [IntegrationRule]
integrationTable =
  [ -- Category 1: Constants (free of integration variable)
    IntegrationRule "constant" matchConstant integrateConstant
  , -- Category 2b: Logarithm (x^(-1)) - try before general power
    IntegrationRule "power_log_x" matchPowerLog integratePowerLog
  , -- Category 2a: General power
    IntegrationRule "power_general" matchPowerGeneral integratePowerGeneral
  , -- Category 3a: Exponential e^x
    IntegrationRule "exp_x" matchExpX integrateExpX
  , -- Category 3b: Natural logarithm
    IntegrationRule "log_x" matchLogX integrateLogX
  , -- Category 3c: General exponential b^x
    IntegrationRule "exp_bx" matchExpBX integrateExpBX
  , -- Category 4: Trigonometric functions
    IntegrationRule "sin_x" matchSinX integrateSinX
  , IntegrationRule "cos_x" matchCosX integrateCosX
  , IntegrationRule "tan_x" matchTanX integrateTanX
  , IntegrationRule "cot_x" matchCotX integrateCotX
  , IntegrationRule "sec_x" matchSecX integrateSecX
  , IntegrationRule "csc_x" matchCscX integrateCscX
  , -- Category 4g-h: Powers of trig functions
    IntegrationRule "sec2_x" matchSec2X integrateSec2X
  , IntegrationRule "csc2_x" matchCsc2X integrateCsc2X
  , -- Category 5: Special composite forms
    IntegrationRule "sec_tan_x" matchSecTanX integrateSecTanX
  , IntegrationRule "csc_cot_x" matchCscCotX integrateCscCotX
  ]

-- ============================================================================

-- * Main Interface

-- ============================================================================

-- | Attempt to integrate an expression using the integration table
-- Returns Just antiderivative if a rule matches, Nothing otherwise
-- Does not include the constant of integration
--
-- Notice that this function only applies the first matching rule from the table and
-- does not attempt to apply multiple rules or combine results.
integrateTable :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateTable var expr = go integrationTable
 where
  go [] = Nothing
  go (rule : rest) =
    if ruleMatcher rule var expr
      -- If the rule matches, attempt to apply it. If application fails (returns Nothing), continue to next rule
      then ruleAntiderivative rule var expr <|> go rest
      else go rest

-- | Linear properties of the integral
-- Attempt to apply linearity rules to `expr` with respect to `var`.
-- Returns `Just antiderivative` when successful, `Nothing` when this
-- linear-property procedure cannot be applied.
--
-- Notice that thie function only applies linearity properties and does not attempt to integrate the resulting parts.
-- It is meant to be used as a step in the overall `integrate` function, which will recursively call `integrate` on the resulting parts.
integrateLinear :: Text -> SimplifiedExpr -> Maybe SimplifiedExpr
integrateLinear var expr = case expr of
  -- Product: separate factors free of the integration variable
  Product' _ ->
    case eitherToMaybe (separateFactors expr (mkSymbol var)) of
      Just (freePart, depPart) ->
        -- If none of the operands is free of x, this property doesn't help
        if freePart == mkNumber 1
          then Nothing
          else case integrate var depPart  of
            Just innerAnti -> eitherToMaybe (freePart .*. innerAnti)
            Nothing        -> Nothing
      Nothing -> Nothing
  -- Sum: integrate each term; if any fails, the whole sum fails
  Sum' terms ->
    let termList = NE.toList terms
        integrated = traverse (integrate var) termList
     in case integrated of
          Just ints -> eitherToMaybe $ simplify $ mkSum (NE.fromList ints)
          Nothing   -> Nothing
  -- Otherwise: cannot apply linearity
  _ -> Nothing

{- | Substitution method (derivative divides method).
Tries candidates from `trialSubstitutions` and checks whether
f / d(v(x))/dx can be rewritten as u(v) that is free of x.
-}
integrateSubstitution :: Text ->SimplifiedExpr -> Maybe SimplifiedExpr
integrateSubstitution (mkSymbol -> xExpr) expr  = do
  dVar <- eitherToMaybe $ mkDiffVar xExpr
  let candidates = sortOn (negate . treeSize) $ filter eligible $ HS.toList $ trialSubstitutions expr
  tryCandidates dVar candidates
 where
  vSym :: SimplifiedExpr
  vSym = mkSymbol "v"

  eligible :: SimplifiedExpr -> Bool
  eligible g = g /= xExpr && not (freeOf g xExpr)

  tryCandidates _ [] = Nothing
  tryCandidates dVar (g : rest) =
    case candidateResult dVar g of
      Just antiderivative -> Just antiderivative
      Nothing             -> tryCandidates dVar rest

  candidateResult dVar g = do
    dgUnsimplified <- eitherToMaybe $ diff (unsimplify g) dVar
    dg <- eitherToMaybe $ simplify dgUnsimplified
    quotient <- eitherToMaybe $ expr ./. dg
    uv <- eitherToMaybe $ subs (Pattern g, Replacement vSym) quotient
    if freeOf uv xExpr
      then do
        inner <- integrate "v" uv
        eitherToMaybe $ subs (Pattern vSym, Replacement g) inner
      else Nothing

{- | Trial substitutions: collect candidate subexpressions suitable for
substitution. This returns a set containing:
 * function applications (Function' name args)
 * arguments of function applications
 * bases and exponents of power expressions
The result is a HashSet of `SimplifiedExpr`.
-}
trialSubstitutions :: SimplifiedExpr -> HS.HashSet SimplifiedExpr
trialSubstitutions expr = HS.foldl' collect HS.empty (completeSubExprs expr)
 where
  collect acc e@(Function' _ args) =
    let acc' = HS.insert e acc
        argSet = HS.fromList (NE.toList args)
     in HS.union acc' argSet
  collect acc (Power' b ex) = HS.insert b $ HS.insert ex acc
  collect acc _ = acc

-- | Main integration function that tries the table, then linear properties, then substitution, and finally expansion
-- Returns Just antiderivative if successful, Nothing otherwise
--
-- Notice that the capability of this function is limited by the patterns in the integration table and the linear/substitution methods implemented.
-- More complex expressions may require additional rules or methods to be added.
--
-- >>> let expr = 2 * "x" ** 3 + 4 * "x" + 5 - tan "x" :: UnsimplifiedExpr
-- >>> fmap toHaskell $ eitherToMaybe (simplify expr) >>= integrate "x"
-- Just "log (cos x) + 5 * x + 2 * x ^ 2 + 1 / 2 * x ^ 4"
--
-- >>> let expr = (cos "x" ** 2) * sin "x" :: UnsimplifiedExpr
-- >>> fmap toHaskell $ eitherToMaybe (simplify expr) >>= integrate "x"
-- Just "(-1) / 3 * (cos x) ^ 3"
integrate :: Text -> SimplifiedExpr  -> Maybe SimplifiedExpr
integrate var expr =
  integrateTable var expr
    <|> integrateLinear var expr
    <|> integrateSubstitution var expr
    -- algebraic expand, if it changes the expression,
    -- try again with the expanded form
    <|> integrateWithExpansion var expr
  where
    integrateWithExpansion v u =
      eitherToMaybe (algebraicExpand u)
        >>= \expanded ->
          if expanded /= u
            then integrate v expanded
            else Nothing
