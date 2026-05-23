-- |
-- Module: SymHask.Symbolic.Polynomial.Generalised
-- Description: Operations on generalised polynomials
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
--
-- Handle polynomials in a generalised sense, where the "variables" can be arbitrary expressions (not just symbols),
-- and the "coefficients" can be any expressions that are free of the variables.
module SymHask.Symbolic.Polynomial.Generalised
    ( -- * Predicates
      isMonomialGpe
    , isPolynomialGpe
    , isRationalGre
      -- * Coefficients
    , coeffVarMonomial
    , coefficientGpe
    , coefficientMonomialGpe
    , leadingCoefficientGpe
      -- * Degrees
    , degreeGpe
      -- * Variables
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
--
-- $setup
-- >>> import SymHask.Printer (toHaskell)
-- >>> import Data.Either.Extra (eitherToMaybe)

-- | Check if an expression is a general monomial in a set of generalized variables.
--
-- Let \(C = \{c_1, c_2, \ldots, c_m\}\) be the set of generalised coefficients
-- and let \(S = \{x_1, x_2, \ldots, x_n\}\) be the set of generalised variables that are not integers or fractions.
-- A general monomial expression (GME) in \(S\) is an expression \(u\) that of the form
--
-- \[
-- c_1 c_2 \dots c_r x^{n_1}_{1} x^{n_2}_{2} \dots x^{n_m}_{m}
-- \]
--
-- where \(r \geq 0\), \(m \geq 0\), each \(n_i\) is a positive integer,
-- and \(c_i\) is free of all variables in \(S\) for each \(i\).
isMonomialGpe :: HS.HashSet SimplifiedExpr -> SimplifiedExpr -> Bool
isMonomialGpe vars u
  | HS.null vars = True
  | u `HS.member` vars = True
  | otherwise = case u of
      Power' b (Number' e) ->
        (b `HS.member` vars && e > 1) || setFreeOf u (HS.toList vars)
      Product' factors ->
        all (isMonomialGpe vars) (NE.toList factors)
      _ -> setFreeOf u (HS.toList vars)

-- | Check if an expression is a general polynomial in a set of generalized variables.
--
-- A general polynomial expression (GPE) in \(S\) is an expression \(u\) that is either
-- a general monomial expression in \(S\), or a sum of two or more general monomial expressions in \(S\).
--
-- >>> let vars = HS.fromList ["x", "y"]
-- >>> let expr = ("x" + 1)**3 + 2*("x" + 1) + 3 :: UnsimplifiedExpr
-- >>> isPolynomialGpe vars <$> (simplify expr)
-- Right False
--
-- >>> let vars = HS.fromList ["x", "y"]
-- >>> let expr = "x"**2*"y" - "x"*"y"**2 + 2 :: UnsimplifiedExpr
-- >>> isPolynomialGpe vars <$> (simplify expr)
-- Right True
isPolynomialGpe :: HS.HashSet SimplifiedExpr -> SimplifiedExpr -> Bool
isPolynomialGpe vars u
  | u `HS.member` vars = True -- Short-circuit: u is itself a generalized variable (GME-2)
  | otherwise = case u of
      Sum' terms -> all (isMonomialGpe vars) (NE.toList terms) -- GPE-2
      _          -> isMonomialGpe vars u -- GPE-1

-- | Check whether an expression is a general rational expression (GRE)
-- in a set of generalized variables.
--
-- A GRE in \(S\) is an expression whose numerator and denominator are both
-- generalized polynomials in \(S\).
--
-- >>> let vars = HS.fromList ["x"]
-- >>> let expr = ("x"**2 - "x" - "y") / ("x" + 4) :: UnsimplifiedExpr
-- >>> isRationalGre vars <$> (simplify expr)
-- Right True
--
-- >>> let vars = HS.fromList ["x"]
-- >>> let expr = "x"**2 + "b"*"x" + "c" :: UnsimplifiedExpr
-- >>> isRationalGre vars <$> (simplify expr)
-- Right True
--
-- The definition also includes GPEs as a special case of GREs (with denominator \(1\)).:
isRationalGre :: HS.HashSet SimplifiedExpr -> SimplifiedExpr -> Bool
isRationalGre vars u =
  either (const False) (isPolynomialGpe vars) (numer u)
    && either (const False) (isPolynomialGpe vars) (denom u)


-- | Extract coefficient and variable parts of a monomial \(u\) w.r.t. a set of generalized variables \((S)\).
--
-- Returns \((c, v)\) where the monomial is \(c \cdot v\).
-- For a monomial that doesn't contain any variables in \(S\), returns \((u, 1)\).
coeffVarMonomial :: HS.HashSet SimplifiedExpr -> SimplifiedExpr -> EvalResult (SimplifiedExpr, SimplifiedExpr)
coeffVarMonomial vars u
  | HS.null vars = pure (u, mkNumber 1)
  | not $ isMonomialGpe vars u =
    Left $ UnsupportedOperation
      "coeffVarMonomial: expression is not a monomial in the given variables"
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
  decomposeProduct :: [SimplifiedExpr] -> HS.HashSet SimplifiedExpr -> EvalResult (SimplifiedExpr, SimplifiedExpr)
  decomposeProduct factors varSet = do
    pairs <- mapM (coeffVarMonomial varSet) factors
    let coeffs = map fst pairs
        varParts = map snd pairs
    coeff <- foldM (.*.) (mkNumber 1) coeffs
    varPart <- foldM (.*.) (mkNumber 1) varParts
    pure (coeff, varPart)

-- | Returns the sum of coefficients parts of all monomials of \(u\) that have the same variable part \(x^j\).
--
-- If there is no monomial with variable part \(x^j\), returns \(0\).
-- Returns `Left` if \(u\) is not a polynomial in \(x\).
--
-- >>> let expr = 3*"x"*"y"**2 + 5*"x"**2*"y" + 7*"x" + 9 :: UnsimplifiedExpr
-- >>> toHaskell <$> ((simplify expr) >>= coefficientGpe "x" 1)
-- Right "7 + 3 * y ^ 2"
coefficientGpe
  :: SimplifiedExpr -- ^ variable \(x\) to extract coefficient for
  -> Integer -- ^ degree \(j\) to extract
  -> SimplifiedExpr -- ^ polynomial expression \(u\)
  -> EvalResult SimplifiedExpr
coefficientGpe x j u
  | j < 0 = pure $ mkNumber 0
  | not (isPolynomialGpe (HS.singleton x) u ) =
    Left $ UnsupportedOperation
      "coefficientGpe: expression is not a polynomial in x"
  | otherwise = case u of
      Sum' terms -> foldM addTerm (mkNumber 0) (NE.toList terms)
      _ -> do
        (c, m) <- coefficientMonomialGpe x u
        if m == j then pure c else pure $ mkNumber 0
 where
  addTerm acc term = do
    (c, m) <- coefficientMonomialGpe x term
    if m == j then acc .+. c else pure acc


-- | Extract (coefficient, degree) for a monomial w.r.t. a single generalized variable.
--
-- Returns `Left` when the operand is not a monomial in the generalized variable.
coefficientMonomialGpe
  :: SimplifiedExpr -- ^ generalized variable \(x\)
  -> SimplifiedExpr -- ^ monomial expression \(u\)
  -> EvalResult (SimplifiedExpr, Integer)
coefficientMonomialGpe x u
  | u == x = pure (mkNumber 1, 1)
  | otherwise = case u of
      Power' b (Number' e) -> handlePowerCase b e
      Product' factors     -> foldM extractProductFactor (u, 0) factors
      _                    -> handleDefaultCase
 where
  handlePowerCase b e
    | b == x && e > 1 = pure (mkNumber 1, e)
    | u `freeOf` x = pure (u, 0)
    | otherwise = Left $
      UnsupportedOperation
        "coefficientMonomialGpe: not a monomial"

  extractProductFactor (coef, deg) factor = do
    (_, deg') <- coefficientMonomialGpe x factor
    if deg' == 0
      then pure (coef, deg) -- no update to coef or deg
      else do
        factorPower <- x .**. mkNumber deg'
        updatedCoef <- coef ./. factorPower
        pure (updatedCoef, deg')

  handleDefaultCase
    | u `freeOf` x = pure (u, 0)
    | otherwise = Left $
      UnsupportedOperation
        "coefficientMonomialGpe: not a monomial"


-- | Extract the leading coefficient of \(u\) with respect to
-- the generalized variable \(x\).
--
-- Returns `Left` when \(u\) is not a GPE in \(x\).
leadingCoefficientGpe
  :: SimplifiedExpr -- ^ generalized variable \(x\)
  -> SimplifiedExpr -- ^ polynomial expression \(u\)
  -> EvalResult SimplifiedExpr
leadingCoefficientGpe x u = do
  degM <- degreeGpe (HS.singleton x) u
  case degM of
    -- zero polynomial: leading coefficient is 0
    Nothing -> pure $ mkNumber 0
    Just d -> case coefficientGpe x d u of
      Left _ -> Left $
        UnsupportedOperation
          "leadingCoefficientGpe: unable to compute leading coefficient"
      Right coeff -> pure coeff



-- | Return the maximum of the degress of all monomials in \(u\) with respect to a
-- generalized variables \(S\).
--
-- Returns `Nothing` for the zero polynomial, and @Just d@ where \(d\) is the degree of the GPE otherwise.
-- Returns `Left` if the expression is not a GPE in the given variables.
--
-- >>> let vars = HS.fromList ["x", "z"]
-- >>> let expr = 2*"x"**2*"y"*"z"**3 + "w"*"x"*"z"**6  :: UnsimplifiedExpr
-- >>> (simplify expr) >>= degreeGpe vars
-- Right (Just 7)
degreeGpe :: HS.HashSet SimplifiedExpr -> SimplifiedExpr -> EvalResult (Maybe Integer)
degreeGpe vars u
  | not (isPolynomialGpe vars u) = Left $ UnsupportedOperation "degreeGpe: expression is not a GPE"
  | isMonomialGpe vars u = pure $ monomialGpeDegree vars u
  | otherwise = case u of
      Sum' terms -> do
        let ds = map (monomialGpeDegree vars) (NE.toList terms)
        if Nothing `elem` ds
          then pure Nothing
          else pure $ Just $ maximum (catMaybes ds)
      _ -> pure $ monomialGpeDegree vars u

-- | Compute degree of a monomial GME: sum of exponents of generalized variables.
-- Returns Nothing for the zero monomial.
--
-- Let \(S = \{x_1, x_2, \ldots, x_n\}\) be the set of generalized variables. Let
-- \[
-- u = c_1 c_2 \dots c_r x^{n_1}_{1} x^{n_2}_{2} \dots x^{n_m}_{m}
-- \]
-- be a monomial expression in \(S\) where \(c_i\) are coefficients and \(n_i\) are positive integers.
-- Then the degree of \(u\) is defined as \(n_1 + n_2 + \dots + n_m\).
--
-- >>> let vars = HS.fromList ["x", "z"]
-- >>> let expr = 3 * "w" * "x"**2 * "y"**3 * "z"**4 :: UnsimplifiedExpr
-- >>> (eitherToMaybe . simplify $ expr) >>= monomialGpeDegree vars
-- Just 6
monomialGpeDegree :: HS.HashSet SimplifiedExpr -> SimplifiedExpr -> Maybe Integer
monomialGpeDegree  _ (Number' 0) = Nothing
monomialGpeDegree  _ (Number' _) = Just 0
monomialGpeDegree  _  (Fraction' _ _)= Just 0
monomialGpeDegree vars expr
  | expr `HS.member` vars = Just 1 -- expr itself is a generalized variable
  | otherwise = case expr of
      Symbol' _ -> Just 0 -- symbol not in vars
      Power' b (Number' e) ->
        if b `HS.member` vars && e > 1 then Just e else Just 0
      Product' factors -> do
        ds <- mapM (monomialGpeDegree vars) (NE.toList factors)
        return $ sum ds
      _ -> Just 0

-- | Compute the natural set of generalized variables for a rational expression.
--
-- A rational variable set is the union of the variables in the numerator and
-- denominator of the expression.
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
