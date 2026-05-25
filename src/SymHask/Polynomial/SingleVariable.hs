-- |
-- Module: SymHask.Polynomial.SingleVariable
-- Description: Operations on single-variable polynomials
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
--
-- Support for operations on polynomials and monomials, including checking
module SymHask.Polynomial.SingleVariable
    ( -- * Predicates
      isMonomialSv
    , isPolynomialSv
      -- * Coefficients
    , coefficientSv
    , leadingCoefficientSv
      -- * Degrees
    , degreeMonomialSv
    , degreeSv
    ) where

import           Control.Applicative             ((<|>))
import           Control.Monad                   (foldM)
import           Data.Either.Extra               (eitherToMaybe)
import           Data.List.NonEmpty              (NonEmpty ((:|)))
import qualified Data.List.NonEmpty              as NE
import           Data.Maybe                      (catMaybes)
import           Data.Text                       (Text)
import           SymHask.Symbolic
import           SymHask.Symbolic.Simplification ((.*.), (.+.))
-- $setup
-- >>> import SymHask.Symbolic

-- | Check whether an expression \(u\) is a monomial in a single variable \(x\).
-- A monomial in \(x\) is defined as:
--
-- MON-1: \(u\) is a `Number` or a `Fraction`
--
-- MON-2: \(u\) is the variable \(x\) itself
--
-- MON-3: \(u\) is of the form \(x^n\) where \(n > 1\) is an integer
--
-- MON-4: \(u\) is a product of monomials in \(x\)
--
-- >>> isMonomialSv "x" <$> (simplify ((2 * "x" ^ 3) :: UnsimplifiedExpr))
-- Right True
--
-- >>> isMonomialSv "x" <$> (simplify ((3 * "y" ^ 2) :: UnsimplifiedExpr))
-- Right False
--
-- >>> isMonomialSv "x" <$> (simplify (("x" + 1) :: UnsimplifiedExpr))
-- Right False
isMonomialSv :: Text ->SimplifiedExpr -> Bool
isMonomialSv _ (Number' _)            = True
isMonomialSv _ (Fraction' _ _)        = True
isMonomialSv x (Symbol' s)            = s == x
isMonomialSv x (Power' b (Number' e)) = b == mkSymbol x && e > 1
isMonomialSv x (Product' factors)     = all (isMonomialSv x) (NE.toList factors)
isMonomialSv _ _                      = False

-- | Check whether an expression is a polynomial in a single variable.
--
-- A polynomial is either a monomial or a sum whose operands are all monomials.
isPolynomialSv :: Text -> SimplifiedExpr -> Bool
isPolynomialSv x expr =
  isMonomialSv x expr || case expr of
    Sum' terms -> all (isMonomialSv x) (NE.toList terms)
    _          -> False

-- | Compute the coefficient of \(x^j\) in a polynomial in a single variable.
--
-- Returns the corresponding coefficient if the expression is a polynomial in \(x\),
-- \(0\) if \(j\) is larger than the degree.
-- Returns `Left` if the expression is not a polynomial in \(x\).
--
-- >>> (simplify ("x"**2 +3*"x" + 5 :: UnsimplifiedExpr)) >>= coefficientSv "x" 1
-- Right (Number 3)
--
-- >>> (simplify (2*"x"**3 + 3*"x" :: UnsimplifiedExpr)) >>= coefficientSv "x" 4
-- Right (Number 0)
--
-- >>> (simplify (("x" + 1) * ("x" + 3) :: UnsimplifiedExpr)) >>= coefficientSv "x" 2
-- Left (UnsupportedOperation "coefficientSv: expression is not a polynomial")
coefficientSv
  :: Text
  -> Integer -- ^ degree \(j\) to extract
  -> SimplifiedExpr
  -> EvalResult SimplifiedExpr
coefficientSv x j expr
  | not (isPolynomialSv x expr) =
      Left $
        UnsupportedOperation
          "coefficientSv: expression is not a polynomial"
  | otherwise = case expr of
      Sum' terms -> foldM addTerm (mkNumber 0) (NE.toList terms)
      _          -> coefficientMonomialSv x expr j
 where
  addTerm acc term = do
    coef <- coefficientMonomialSv x term j
    acc .+. coef

-- | For a monomial of degree \(j\),
-- extract coefficient directly from the monomial summary.
coefficientMonomialSv
  :: Text
  -> SimplifiedExpr
  -> Integer  -- ^ degree \(j\) to extract
  -> EvalResult SimplifiedExpr
coefficientMonomialSv x expr j
  | not (isMonomialSv x expr) = pure $ mkNumber 0
  | j < 0 = pure $ mkNumber 0
  | otherwise = case monomialSummary x expr of
      Just (coeff, degree)
        | degree == j -> pure coeff
        | otherwise -> pure $ mkNumber 0
      Nothing -> pure $ mkNumber 0

-- | Compute the leading coefficient of a polynomial in a single variable.
--
-- If the expression is a polynomial in \(x\), returns the coefficient of \(x^d\) ,
-- where \(d\) is the degree of the polynomial.
-- Otherwise returns an error.
--
-- >>> (simplify (("x"**2 + 3*"x" + 5) :: UnsimplifiedExpr)) >>= leadingCoefficientSv "x"
-- Right (Number 1)
--
-- >>> (simplify ((3) :: UnsimplifiedExpr)) >>= leadingCoefficientSv "x"
-- Right (Number 3)
leadingCoefficientSv :: Text -> SimplifiedExpr -> EvalResult SimplifiedExpr
leadingCoefficientSv x expr =
  case degreeSv x expr of
    Nothing ->
      Left $
        UnsupportedOperation
          "leadingCoefficientSv: expression is not a polynomial"
    Just degree ->
      case coefficientSv x degree expr of
        Left _ ->
          Left $
            UnsupportedOperation
              "leadingCoefficientSv: unable to compute leading coefficient"
        Right coeff -> pure coeff


-- | Compute the degree of a polynomial in a single variable.
--
-- For a monomial, returns its degree.
-- For a sum of monomials, returns the maximum degree among all terms.
-- Returns `Nothing` if the expression is not polynomial in \(x\).
--
-- >>> degreeSv "x" <$> (simplify ((2 * "x" ^ 3 + 4 * "x" + 5) :: UnsimplifiedExpr))
-- Right (Just 3)
--
-- >>> degreeSv "x" <$> (simplify ((2 * "x" ^ 3) :: UnsimplifiedExpr))
-- Right (Just 3)
--
-- >>> degreeSv "x" <$> (simplify ((("x" + 1) * ("x" + 3)) :: UnsimplifiedExpr))
-- Right Nothing
--
-- >>> degreeSv "x" <$> (simplify ((3) :: UnsimplifiedExpr))
-- Right (Just 0)
degreeSv :: Text -> SimplifiedExpr -> Maybe Integer
degreeSv x expr =
  degreeMonomialSv x expr <|> case expr of
    Sum' terms ->
      let degrees = [degreeMonomialSv x term | term <- NE.toList terms]
       in if Nothing `notElem` degrees
            then Just $ maximum (catMaybes degrees)
            else Nothing
    _ -> Nothing

-- | Compute the degree of a monomial in a single variable.
--
-- >>> degreeMonomialSv "x" <$> (simplify ((2 * "x" ^ 3) :: UnsimplifiedExpr))
-- Right (Just 3)
--
-- >>> degreeMonomialSv "x" <$> (simplify ((3) :: UnsimplifiedExpr))
-- Right (Just 0)
--
-- >>> degreeMonomialSv "x" <$> (simplify (("x" + 1) :: UnsimplifiedExpr))
-- Right Nothing
--
-- If the expression is a monomial in x, returns Just its degree.
-- For constants, the degree is 0.
-- Returns Nothing if the expression is not a monomial in x.
degreeMonomialSv :: Text -> SimplifiedExpr -> Maybe Integer
degreeMonomialSv x expr = snd <$> monomialSummary x expr

-- | Extract (coefficient, degree) for a monomial in x.
--
-- Returns Just (coeff, deg) if the expression is a monomial in x,
-- where coeff is the coefficient and deg is the exponent of x.
-- For constants, deg = 0.
-- Returns Nothing if the expression is not a monomial.
monomialSummary :: Text -> SimplifiedExpr -> Maybe (SimplifiedExpr, Integer)
monomialSummary _ (Number' 0) = Nothing -- Zero is special (degree -∞)
monomialSummary _ (Number' n) = Just (mkNumber n, 0)
monomialSummary _ expr@(Fraction' _ _) = Just (expr, 0)
monomialSummary x (Symbol' s)
  | s == x = Just (mkNumber 1, 1)
  | otherwise = Nothing
monomialSummary x (Power' b (Number' e))
  | b == mkSymbol x = Just (mkNumber 1, e)
  | otherwise = Nothing
monomialSummary x (Product' (f1 :| [f2])) = do
  (coeff1, deg1) <- monomialSummary x f1
  (coeff2, deg2) <- monomialSummary x f2
  coeff <- eitherToMaybe $ coeff1 .*. coeff2
  pure (coeff, deg1 + deg2)
monomialSummary _ _ = Nothing
