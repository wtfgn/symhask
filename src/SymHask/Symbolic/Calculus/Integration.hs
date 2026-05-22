{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}

module SymHask.Symbolic.Calculus.Integration
    ( IntegrationVar
    , integrate
    , integrateLinear
    , integrateTable
    , mkIntegrationVar
    ) where

import           Control.Applicative                       ((<|>))
import           Control.Monad.Error.Class                 (MonadError (throwError))
import           Data.Either.Extra                         (eitherToMaybe)
import qualified Data.HashSet                              as HS
import           Data.List                                 (find, sortOn)
import           Data.List.NonEmpty                        (NonEmpty ((:|)))
import qualified Data.List.NonEmpty                        as NE
import           Data.Text                                 (Text)
import           SymHask.Symbolic
import           SymHask.Symbolic.Basic                    (Pattern (..),
                                                            Replacement (..),
                                                            freeOf,
                                                            separateFactors,
                                                            subs, treeSize,
                                                            trialSubstitutions)
import           SymHask.Symbolic.Calculus.Differentiation (diff, mkDiffVar)
import           SymHask.Symbolic.Polynomial               (algebraicExpand)
import           SymHask.Symbolic.Simplification           ((.**.), (.*.),
                                                            (./.))

-- ============================================================================

-- * Data Types

-- ============================================================================

-- | Integration variable, similar to DiffVar
newtype IntegrationVar
  = IntSymbol Text
  deriving (Eq, Show)

-- | Rule in the integration table
data IntegrationRule
  = IntegrationRule
      { ruleName :: Text
        -- Description of the rule
      , ruleMatcher :: SimplifiedExpr -> IntegrationVar -> Bool
        -- Does this rule match?
      , ruleAntiderivative :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
        -- Apply the rule to get antiderivative (or Nothing if application fails)
      }

-- ============================================================================

-- * Helpers

-- ============================================================================

-- | Convert an integration variable back to an expression
integrationVarToExpr :: IntegrationVar -> Expr a
integrationVarToExpr (IntSymbol s) = mkSymbol s

-- integrationVarToExpr (IntFunction fname args) =
--   let args' = NE.fromList $ map mkSymbol (NE.toList args)
--   in mkFunction fname args'

-- | Create an integration variable from an expression
mkIntegrationVar :: Expr s -> EvalResult IntegrationVar
mkIntegrationVar (Symbol' s) = pure $ IntSymbol s
-- mkIntegrationVar (Function' fname args) =
--   let argNames = [ s | Symbol' s <- NE.toList args ]
--   in pure $ IntFunction fname (NE.fromList argNames)
mkIntegrationVar _ =
  throwError $
    UnsupportedOperation "Cannot create IntegrationVar from this expression type"

-- | Check if an expression is free of the integration variable
isFreeOf :: SimplifiedExpr -> IntegrationVar -> Bool
isFreeOf expr (IntSymbol s) = freeOf expr (mkSymbol s)

-- isFreeOf expr (IntFunction fname args) =
--   let funcExpr = integrationVarToExpr (IntFunction fname args)
--   in freeOf expr funcExpr

-- ============================================================================

-- * Category Matchers

-- ============================================================================

{- | Category 1: Constants (free of integration variable)
∫ c dx = c*x
-}
matchConstant :: SimplifiedExpr -> IntegrationVar -> Bool
matchConstant = isFreeOf

-- This computes:
integrateConstant :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateConstant c (IntSymbol x) = eitherToMaybe (c .*. mkSymbol x)

-- integrateConstant c (IntFunction fname args) =
--   let var = integrationVarToExpr (IntFunction fname args)
--   in Just $ c .*. var

{- | Category 2a: Power rule for x^n where n != -1
∫ x^n dx = x^(n+1) / (n+1) where n is free of x
-}
matchPowerGeneral :: SimplifiedExpr -> IntegrationVar -> Bool
matchPowerGeneral expr var = case expr of
  -- handle implicit exponent 1: Symbol 'x' treated as x^1
  Symbol' s | s == getVarName var -> True
  Power' (Symbol' s) n | s == getVarName var && n `isFreeOf` var && isNotMinusOne n -> True
  _ -> False
 where
  isNotMinusOne (Number' (-1)) = False
  isNotMinusOne _              = True
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integratePowerGeneral :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integratePowerGeneral expr _ = case expr of
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
matchPowerLog :: SimplifiedExpr -> IntegrationVar -> Bool
matchPowerLog expr var = case expr of
  Power' (Symbol' s) (Number' (-1)) | s == getVarName var -> True
  Quotient' (Number' 1) (Symbol' s) | s == getVarName var -> True
  _                                                       -> False
 where
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integratePowerLog :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integratePowerLog _ (IntSymbol x) = Just $ mkFunction "log" (mkSymbol x :| [])

-- integratePowerLog _ (IntFunction fname args) =
--   let funcExpr = integrationVarToExpr (IntFunction fname args)
--   in Just $ mkFunction "log" (funcExpr :| [])

{- | Category 3a: Exponential e^x
∫ e^x dx = e^x
-}
matchExpX :: SimplifiedExpr -> IntegrationVar -> Bool
matchExpX expr var = case expr of
  Exp' (Symbol' s) | s == getVarName var -> True
  _                                      -> False
 where
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integrateExpX :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateExpX (Exp' x) _ = Just $ mkFunction "exp" (x :| [])
integrateExpX _ _        = Nothing

{- | Category 3b: Natural logarithm ln(x)
∫ ln(x) dx = x*ln(x) - x
-}
matchLogX :: SimplifiedExpr -> IntegrationVar -> Bool
matchLogX expr var = case expr of
  Log' (Symbol' s) | s == getVarName var -> True
  _                                      -> False
 where
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integrateLogX :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateLogX _ (IntSymbol x) =
  let xSym = mkSymbol x :: UnsimplifiedExpr
      res = simplify $ (xSym * mkFunction "log" (xSym :| [])) - xSym
   in eitherToMaybe res

{- | Category 3c: General exponential b^x where b is free of x
∫ b^x dx = b^x / ln(b)
-}
matchExpBX :: SimplifiedExpr -> IntegrationVar -> Bool
matchExpBX expr var = case expr of
  Power' b (Symbol' s) | isFreeOf b var && s == getVarName var -> True
  _                                                            -> False
 where
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integrateExpBX :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateExpBX (Power' (unsimplify -> b) (unsimplify -> x)) _ =
  eitherToMaybe $ simplify $ (b ** x) / mkFunction "log" (b :| [])
integrateExpBX _ _ = Nothing

{- | Category 4a: sin(x)
∫ sin(x) dx = -cos(x)
-}
matchSinX :: SimplifiedExpr -> IntegrationVar -> Bool
matchSinX expr var = case expr of
  Sin' (Symbol' s) | s == getVarName var -> True
  _                                      -> False
 where
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integrateSinX :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateSinX (Sin' x) _ = eitherToMaybe $ simplify $ mkUnaryDiff (mkFunction "cos" (x :| []))
integrateSinX _ _ = Nothing

{- | Category 4b: cos(x)
∫ cos(x) dx = sin(x)
-}
matchCosX :: SimplifiedExpr -> IntegrationVar -> Bool
matchCosX expr var = case expr of
  Cos' (Symbol' s) | s == getVarName var -> True
  _                                      -> False
 where
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integrateCosX :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateCosX (Cos' x) _ = Just $ mkFunction "sin" (x :| [])
integrateCosX _ _        = Nothing

{- | Category 4c: tan(x)
∫ tan(x) dx = -ln(cos(x)) or ln(|sec(x)|), use -ln(cos(x))
-}
matchTanX :: SimplifiedExpr -> IntegrationVar -> Bool
matchTanX expr var = case expr of
  Tan' (Symbol' s) | s == getVarName var -> True
  _                                      -> False
 where
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integrateTanX :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateTanX (Tan' x) _ =
  eitherToMaybe $ simplify $ mkUnaryDiff (mkFunction "log" (mkFunction "cos" (x :| []) :| []))
integrateTanX _ _ = Nothing

{- | Category 4d: cot(x)
∫ cot(x) dx = ln(sin(x))
-}
matchCotX :: SimplifiedExpr -> IntegrationVar -> Bool
matchCotX expr var = case expr of
  Cot' (Symbol' s) | s == getVarName var -> True
  _                                      -> False
 where
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integrateCotX :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateCotX (Cot' x) _ = Just $ mkFunction "log" (mkFunction "sin" (x :| []) :| [])
integrateCotX _ _ = Nothing

{- | Category 4e: sec(x)
∫ sec(x) dx = ln(sec(x) + tan(x))
-}
matchSecX :: SimplifiedExpr -> IntegrationVar -> Bool
matchSecX expr var = case expr of
  Sec' (Symbol' s) | s == getVarName var -> True
  _                                      -> False
 where
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integrateSecX :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateSecX (Sec' (unsimplify -> x)) _ =
  let secX = mkFunction "sec" (x :| [])
      tanX = mkFunction "tan" (x :| [])
   in eitherToMaybe $ simplify $ mkFunction "log" ((secX + tanX) :| [])
integrateSecX _ _ = Nothing

{- | Category 4f: csc(x)
∫ csc(x) dx = -ln(csc(x) + cot(x))
-}
matchCscX :: SimplifiedExpr -> IntegrationVar -> Bool
matchCscX expr var = case expr of
  Csc' (Symbol' s) | s == getVarName var -> True
  _                                      -> False
 where
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integrateCscX :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateCscX (Csc' (unsimplify -> x)) _ =
  let cscX = mkFunction "csc" (x :| [])
      cotX = mkFunction "cot" (x :| [])
   in eitherToMaybe $ simplify $ mkUnaryDiff (mkFunction "log" ((cscX + cotX) :| []))
integrateCscX _ _ = Nothing

{- | Category 4g: sec^2(x)
∫ sec^2(x) dx = tan(x)
-}
matchSec2X :: SimplifiedExpr -> IntegrationVar -> Bool
matchSec2X expr var = case expr of
  Power' (Sec' (Symbol' s)) (Number' 2) | s == getVarName var -> True
  _                                                           -> False
 where
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integrateSec2X :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateSec2X (Power' (Sec' x) _) _ = eitherToMaybe $ simplify $ mkFunction "tan" (x :| [])
integrateSec2X _ _ = Nothing

{- | Category 4h: csc^2(x)
∫ csc^2(x) dx = -cot(x)
-}
matchCsc2X :: SimplifiedExpr -> IntegrationVar -> Bool
matchCsc2X expr var = case expr of
  Power' (Csc' (Symbol' s)) (Number' 2) | s == getVarName var -> True
  _                                                           -> False
 where
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integrateCsc2X :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateCsc2X (Power' (Csc' x) _) _ = eitherToMaybe $ simplify $ mkUnaryDiff (mkFunction "cot" (x :| []))
integrateCsc2X _ _ = Nothing

-- | Category 5: Special forms from derivatives of trig/inverse trig functions

{- | Category 5a: sec(x)*tan(x)
∫ sec(x)*tan(x) dx = sec(x)
-}
matchSecTanX :: SimplifiedExpr -> IntegrationVar -> Bool
matchSecTanX expr var = case expr of
  Product' factors | check factors -> True
  _                                -> False
 where
  check = liftA2 (&&) hasSecX hasTanX
  hasSecX = any (\case Sec' (Symbol' s) | s == getVarName var -> True; _ -> False)
  hasTanX = any (\case Tan' (Symbol' s) | s == getVarName var -> True; _ -> False)
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integrateSecTanX :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateSecTanX (Product' factors) var = do
  let secFactor = find (\case Sec' (Symbol' s) | s == getVarName var -> True; _ -> False) factors
  secFactor >>= \(Sec' x) -> Just $ mkFunction "sec" (x :| [])
 where
  getVarName (IntSymbol s) = s
-- getVarName (IntFunction fname _) = fname
integrateSecTanX _ _ = Nothing

{- | Category 5b: csc(x)*cot(x)
∫ csc(x)*cot(x) dx = -csc(x)
-}
matchCscCotX :: SimplifiedExpr -> IntegrationVar -> Bool
matchCscCotX expr var = case expr of
  Product' factors | check factors -> True
  _                                -> False
 where
  check = liftA2 (&&) hasCscX hasCotX
  hasCscX = any (\case Csc' (Symbol' s) | s == getVarName var -> True; _ -> False)
  hasCotX = any (\case Cot' (Symbol' s) | s == getVarName var -> True; _ -> False)
  getVarName (IntSymbol s) = s

-- getVarName (IntFunction fname _) = fname

integrateCscCotX :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateCscCotX (Product' factors) var = do
  let cscFactor = find (\case Csc' (Symbol' s) | s == getVarName var -> True; _ -> False) factors
  cscFactor >>= \(Csc' x) -> eitherToMaybe $ simplify $ mkUnaryDiff (mkFunction "csc" (x :| []))
 where
  getVarName (IntSymbol s) = s
-- getVarName (IntFunction fname _) = fname
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

{- | Attempt to integrate an expression using the integration table
Returns Just antiderivative if a rule matches, Nothing otherwise
Does not include the constant of integration
-}
integrateTable :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateTable expr var = go integrationTable
 where
  go [] = Nothing
  go (rule : rest) =
    if ruleMatcher rule expr var
      -- If the rule matches, attempt to apply it. If application fails (returns Nothing), continue to next rule
      then ruleAntiderivative rule expr var <|> go rest
      else go rest

{- | Linear properties of the integral
Attempt to apply linearity rules to `expr` with respect to `var`.
Returns `Just antiderivative` when successful, `Nothing` when this
linear-property procedure cannot be applied.
-}
integrateLinear :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateLinear expr var = case expr of
  -- Product: separate factors free of the integration variable
  Product' _ ->
    case eitherToMaybe (separateFactors expr (integrationVarToExpr var)) of
      Just (freePart, depPart) ->
        -- If none of the operands is free of x, this property doesn't help
        if freePart == mkNumber 1
          then Nothing
          else case integrate depPart var of
            Just innerAnti -> eitherToMaybe (freePart .*. innerAnti)
            Nothing        -> Nothing
      Nothing -> Nothing
  -- Sum: integrate each term; if any fails, the whole sum fails
  Sum' terms ->
    let termList = NE.toList terms
        integrated = traverse (`integrate` var) termList
     in case integrated of
          Just ints -> eitherToMaybe $ simplify $ mkSum (NE.fromList ints)
          Nothing   -> Nothing
  -- Otherwise: cannot apply linearity
  _ -> Nothing

{- | Substitution method (derivative divides method).
Tries candidates from `trialSubstitutions` and checks whether
f / d(v(x))/dx can be rewritten as u(v) that is free of x.
-}
integrateSubstitution :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrateSubstitution expr (integrationVarToExpr -> xExpr) = do
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
        inner <- integrate uv (IntSymbol "v")
        eitherToMaybe $ subs (Pattern vSym, Replacement g) inner
      else Nothing

integrate :: SimplifiedExpr -> IntegrationVar -> Maybe SimplifiedExpr
integrate expr var =
  integrateTable expr var
    <|> integrateLinear expr var
    <|> integrateSubstitution expr var
    -- algebraic expand, if it changes the expression, try again with the expanded form
    <|> ( eitherToMaybe (algebraicExpand expr)
            >>= \expanded ->
              if expanded /= expr
                then integrate expanded var
                else Nothing
        )
