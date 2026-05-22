module SymHask.Symbolic.Polynomial.Generalised
    ( coeffVarMonomial
    , coefficientGpe
    , coefficientMonomialGpe
    , degreeGpe
    , isMonomialGpe
    , isPolynomialGpe
    , isRationalGre
    , leadingCoefficientGpe
    , rationalVariables
    , variables
    ) where

import           Control.Monad                        (foldM)
import qualified Data.HashSet                         as HS
import qualified Data.List.NonEmpty                   as NE
import           Data.Maybe                           (catMaybes)
import           SymHask.Symbolic
import           SymHask.Symbolic.Basic               (freeOf, setFreeOf)
import           SymHask.Symbolic.Polynomial.Rational (denom, numer)
import           SymHask.Symbolic.Simplification      ((.**.), (.*.), (.+.),
                                                       (./.))

{- | Check if an expression is a general monomial in a set of generalized variables.

A GME in S = {x₁, x₂, ..., xₘ} satisfies one of:
- GME-1: Free of all variables in S
- GME-2: u is a member of S
- GME-3: u = x^n where x ∈ S and n > 1 is an integer
- GME-4: u is a product where each operand is a GME in S
-}
isMonomialGpe :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> Bool
isMonomialGpe u vars
  | HS.null vars = True
  | u `HS.member` vars = True -- GME-2: u is a generalized variable
  | otherwise = case u of
      Power' b (Number' e) ->
        -- GME-3: x^n where x in vars and n > 1
        (b `HS.member` vars && e > 1) || setFreeOf u (HS.toList vars)
      Product' factors ->
        all (`isMonomialGpe` vars) (NE.toList factors) -- GME-4: product of GMEs
      _ -> setFreeOf u (HS.toList vars) -- GME-1: free of all variables

{- | Check if an expression is a general polynomial in a set of generalized variables.

A GPE in S satisfies one of:
- GPE-1: u is a GME in S
- GPE-2: u is a sum where each operand is a GME in S
-}
isPolynomialGpe :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> Bool
isPolynomialGpe u vars
  | u `HS.member` vars = True -- Short-circuit: u is itself a generalized variable (GME-2)
  | otherwise = case u of
      Sum' terms -> all (`isMonomialGpe` vars) (NE.toList terms) -- GPE-2
      _          -> isMonomialGpe u vars -- GPE-1

{- | Check whether an expression is a general rational expression (GRE)
in a set of generalized variables.

A GRE in S is an expression whose numerator and denominator are both
generalized polynomials in S.
-}
isRationalGre :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> Bool
isRationalGre u vars =
  either (const False) (`isPolynomialGpe` vars) (numer u)
    && either (const False) (`isPolynomialGpe` vars) (denom u)

{- | Compute the natural set of generalized variables for a rational expression.

A rational variable set is the union of the variables in the numerator and
denominator of the expression.
-}
rationalVariables :: SimplifiedExpr -> EvalResult (HS.HashSet SimplifiedExpr)
rationalVariables u = do
  n <- numer u
  d <- denom u
  pure $ variables n `HS.union` variables d

-- | Compute the natural set of generalized variables for an expression.
variables :: SimplifiedExpr -> HS.HashSet SimplifiedExpr
variables = \case
  Number' _ -> HS.empty -- VAR-1
  Fraction' _ _ -> HS.empty -- VAR-1
  Power' b (Number' e)
    | e > 1 -> HS.singleton b -- VAR-2 (integer exponent > 1)
  p@(Power' _ _) -> HS.singleton p -- VAR-2 otherwise: include the power itself
  Sum' terms -> foldMap variables (NE.toList terms) -- VAR-3
  Product' factors -> foldMap varForFactors (NE.toList factors) -- VAR-4
  expr -> HS.singleton expr -- VAR-5
 where
  varForFactors :: SimplifiedExpr -> HS.HashSet SimplifiedExpr
  varForFactors (Number' _) = HS.empty
  varForFactors (Fraction' _ _) = HS.empty
  varForFactors (Power' b (Number' e))
    | e > 1 = HS.singleton b
  varForFactors p@(Power' _ _) = HS.singleton p
  varForFactors s@(Sum' _) = HS.singleton s
  varForFactors factor = variables factor

{- | Degree for general polynomial expressions (GPE).
Returns Left if the expression is not a GPE in the given set of generalized variables.
Otherwise returns Right (Just n) for degree n, or Right Nothing to represent -∞ (zero polynomial).
-}
degreeGpe :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> EvalResult (Maybe Integer)
degreeGpe u vars
  | not (isPolynomialGpe u vars) = Left $ UnsupportedOperation "degreeGpe: expression is not a GPE"
  | isMonomialGpe u vars = pure $ monomialGpeDegree u vars
  | otherwise = case u of
      Sum' terms -> do
        let ds = map (`monomialGpeDegree` vars) (NE.toList terms)
        if Nothing `elem` ds
          then pure Nothing
          else pure $ Just $ maximum (catMaybes ds)
      _ -> pure $ monomialGpeDegree u vars

{- | Compute degree of a monomial GME: sum of exponents of generalized variables.
Returns Nothing for the zero monomial.
-}
monomialGpeDegree :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> Maybe Integer
monomialGpeDegree (Number' 0) _ = Nothing
monomialGpeDegree (Number' _) _ = Just 0
monomialGpeDegree (Fraction' _ _) _ = Just 0
monomialGpeDegree expr vars
  | expr `HS.member` vars = Just 1 -- expr itself is a generalized variable
  | otherwise = case expr of
      Symbol' _ -> Just 0 -- symbol not in vars
      Power' b (Number' e) ->
        if b `HS.member` vars && e > 1 then Just e else Just 0
      Product' factors -> do
        ds <- mapM (`monomialGpeDegree` vars) (NE.toList factors)
        return $ sum ds
      _ -> Just 0

{- | Extract (coefficient, degree) for a monomial w.r.t. a single generalized variable.
Returns Left when the operand is not a monomial in the generalized variable.
-}
coefficientMonomialGpe :: SimplifiedExpr -> SimplifiedExpr -> EvalResult (SimplifiedExpr, Integer)
coefficientMonomialGpe u x
  | u == x = pure (mkNumber 1, 1)
  | otherwise = case u of
      Power' b (Number' e) -> handlePowerCase b e
      Product' factors     -> foldM extractProductFactor (u, 0) factors
      _                    -> handleDefaultCase
 where
  handlePowerCase b e
    | b == x && e > 1 = pure (mkNumber 1, e)
    | u `freeOf` x = pure (u, 0)
    | otherwise = Left $ UnsupportedOperation "coefficientMonomialGpe: not a monomial"

  extractProductFactor (coef, deg) factor = do
    (_, deg') <- coefficientMonomialGpe factor x
    if deg' == 0
      then pure (coef, deg) -- no update to coef or deg
      else do
        factorPower <- x .**. mkNumber deg'
        updatedCoef <- coef ./. factorPower
        pure (updatedCoef, deg')

  handleDefaultCase
    | u `freeOf` x = pure (u, 0)
    | otherwise = Left $ UnsupportedOperation "coefficientMonomialGpe: not a monomial"

{- | Coefficient_gpe(u, x, j): coefficient of x^j in polynomial u (generalized var x).
Returns Left if u is not a polynomial in x; otherwise returns the coefficient (possibly 0).
-}
coefficientGpe :: SimplifiedExpr -> SimplifiedExpr -> Integer -> EvalResult SimplifiedExpr
coefficientGpe u x j
  | j < 0 = pure $ mkNumber 0
  | not (isPolynomialGpe u (HS.singleton x)) = Left $ UnsupportedOperation "coefficientGpe: expression is not a polynomial in x"
  | otherwise = case u of
      Sum' terms -> foldM addTerm (mkNumber 0) (NE.toList terms)
      _ -> do
        (c, m) <- coefficientMonomialGpe u x
        if m == j then pure c else pure $ mkNumber 0
 where
  addTerm acc term = do
    (c, m) <- coefficientMonomialGpe term x
    if m == j then acc .+. c else pure acc

{- | Leading_coefficient_gpe(u, x): leading coefficient of u with respect to
the generalized variable x. Returns Left when u is not a GPE in x.
-}
leadingCoefficientGpe :: SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
leadingCoefficientGpe u x = do
  degM <- degreeGpe u (HS.singleton x)
  case degM of
    -- zero polynomial: leading coefficient is 0
    Nothing -> pure $ mkNumber 0
    Just d -> case coefficientGpe u x d of
      Left _ -> Left $ UnsupportedOperation "leadingCoefficientGpe: unable to compute leading coefficient"
      Right coeff -> pure coeff

{- | Extract coefficient and variable parts of a monomial w.r.t. a set of generalized variables.
Returns (coefficient, variable_part) where the monomial = coefficient * variable_part.
For a monomial that doesn't contain any variables in S, returns (monomial, 1).
-}
coeffVarMonomial :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> EvalResult (SimplifiedExpr, SimplifiedExpr)
coeffVarMonomial u vars
  | HS.null vars = pure (u, mkNumber 1)
  | not $ isMonomialGpe u vars = Left $ UnsupportedOperation "coeffVarMonomial: expression is a monomial, not a product of coefficient and variable part"
  | setFreeOf u (HS.toList vars) = pure (u, mkNumber 1)
  | u `HS.member` vars = pure (mkNumber 1, u) -- u itself is a variable
  | otherwise = case u of
      Number' _ -> pure (u, mkNumber 1)
      Fraction' _ _ -> pure (u, mkNumber 1)
      Power' b (Number' e) ->
        if b `HS.member` vars && e > 1
          then pure (mkNumber 1, u) -- power of variable
          else pure (u, mkNumber 1)
      Product' factors -> decomposeProduct (NE.toList factors) vars
      _ -> pure (u, mkNumber 1)
 where
  decomposeProduct factors varSet = do
    pairs <- mapM (`coeffVarMonomial` varSet) factors
    let coeffs = map fst pairs
        varParts = map snd pairs
    coeff <- foldM (.*.) (mkNumber 1) coeffs
    varPart <- foldM (.*.) (mkNumber 1) varParts
    pure (coeff, varPart)
