-- |
-- Module: SymHask.Polynomial.Rational
-- Description: Operations on rational expressions
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
--
-- Support for operations on rational expressions, including extracting numerators and denominators,
-- and transforming expressions into rationalized form.
module SymHask.Polynomial.Rational
    ( -- * Rationalization
      rationalise
      -- * Utilities
    , denom
    , numer
    ) where

import           Data.List.NonEmpty              (NonEmpty ((:|)))
import qualified Data.List.NonEmpty              as NE
import           SymHask.Symbolic
import           SymHask.Symbolic.Basic          (buildRestProduct,
                                                  buildRestSum)
import           SymHask.Symbolic.Simplification ((.**.), (.*.), (.+.), (./.))

--
-- $setup
-- >>> import SymHask.Printer.Haskell

-- | Rationalise an expression by transforming it into a single fraction.
--
-- >>> toHaskell <$> (simplify (1 + 1/"x" :: UnsimplifiedExpr) >>=rationalise)
-- Right "x ^ (-1) * (1 + x)"
rationalise :: SimplifiedExpr -> EvalResult SimplifiedExpr
rationalise u = case u of
  Power' base expn -> do
    base' <- rationalise base
    base' .**. expn
  Product' (f :| []) -> rationalise f
  Product' (f :| rest) -> do
    restProd <- buildRestProduct rest
    left <- rationalise f
    right <- rationalise restProd
    left .*. right
  Sum' (f :| []) -> rationalise f
  Sum' (f :| rest) -> do
    restSum <- buildRestSum rest
    g <- rationalise f
    r <- rationalise restSum
    rationaliseSum g r
  _ -> pure u

-- | Rationalize a sum of two already-rationalized expressions.
--
-- Uses the transformation m/r + n/s -> (m*s + n*r)/(r*s), and repeats
-- until both addends are denominator-free.
rationaliseSum :: SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
rationaliseSum u v = do
  m <- numer u
  r <- denom u
  n <- numer v
  s <- denom v
  if r == mkNumber 1 && s == mkNumber 1
    then u .+. v
    else do
      ms <- m .*. s
      nr <- n .*. r
      top <- ms .+. nr
      bot <- r .*. s
      merged <- top ./. bot
      rationalise merged

-- | Returns the numerator of an expression
--
-- For a `Fraction`, this is the numerator component.
--
-- For a `Power`, if the exponent is negative, the numerator is \(1\); otherwise it's the expression itself.
--
-- For a `Product`, the numerator is the product of the numerators of the factors.
--
-- For all other expressions, the numerator is the expression itself.
--
-- >>> toHaskell <$> (simplify ((mkFraction 6 4) :: UnsimplifiedExpr) >>= numer)
-- Right "3"
--
-- >>> let expr = 2/3 * ("x"*("x" + 1))/("x" + 2) * "y"**"n" :: UnsimplifiedExpr
-- >>> toHaskell <$> (simplify expr >>= numer)
-- Right "2 * x * (1 + x) * y ^ n"
numer :: SimplifiedExpr -> EvalResult SimplifiedExpr
numer (Fraction' n _) = pure $ mkNumber n
numer u@(Power' _ (Number' e)) =
  if e < 0 then pure $ mkNumber 1 else pure u
numer u@(Power' _ (Fraction' num _)) =
  if num < 0 then pure $ mkNumber 1 else pure u
numer (Product' (f :| rest)) = do
  fNum <- numer f
  rest' <- simplify . mkProduct . NE.fromList $ rest
  restNum <- numer rest'
  fNum .*. restNum
numer u = pure u

-- | Returns the denominator of an expression
--
-- For a `Fraction`, this is the denominator component.
--
-- For a `Power`, if the exponent is negative, the denominator is the expression itself; otherwise it's \(1\).
--
-- For a `Product`, the denominator is the product of the denominators of the factors.
--
-- For all other expressions, the denominator is \(1\).
--
-- >>> toHaskell <$> (simplify ((mkFraction 6 4) :: UnsimplifiedExpr) >>= denom)
-- Right "2"
--
-- >>> let expr = 2/3 * ("x"*("x" + 1))/("x" + 2) * "y"**"n" :: UnsimplifiedExpr
-- >>> toHaskell <$> (simplify expr >>= denom)
-- Right "3 * (2 + x)"
denom :: SimplifiedExpr -> EvalResult SimplifiedExpr
denom (Fraction' _ d) = pure $ mkNumber d
denom u@(Power' _ (Number' e)) =
  if e < 0
    then simplify $ mkPower u (mkNumber (-1))
    else pure $ mkNumber 1
denom u@(Power' _ (Fraction' num _)) =
  if num < 0
    then simplify $ mkPower u (mkNumber (-1))
    else pure $ mkNumber 1
denom (Product' (f :| rest)) = do
  fDenom <- denom f
  rest' <- simplify . mkProduct . NE.fromList $ rest
  restDenom <- denom rest'
  fDenom .*. restDenom
denom _ = pure $ mkNumber 1
