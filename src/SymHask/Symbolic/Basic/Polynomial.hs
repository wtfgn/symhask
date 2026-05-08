module SymHask.Symbolic.Basic.Polynomial
  ( isMonomialSv
  , isPolynomialSv
  ) where

import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Text (Text)
import SymHask.Symbolic

-- | Check whether an expression is a monomial in a single variable.
--
-- This follows the computational definition from the chapter:
-- constants, the variable itself, powers of the variable with integer
-- exponent greater than one, and products of monomials are monomials.
isMonomialSv :: SimplifiedExpr -> Text -> Bool
isMonomialSv (Number' _) _ = True
isMonomialSv (Fraction' _ _) _ = True
isMonomialSv (Symbol' s) x = s == x
isMonomialSv (Power' b e) x = b == mkSymbol x && isPositiveInteger e
isMonomialSv (Product' factors) x = all (`isMonomialSv` x) (NE.toList factors)
isMonomialSv _ _ = False

-- | Check whether an expression is a polynomial in a single variable.
--
-- A polynomial is either a monomial or a sum whose operands are all monomials.
isPolynomialSv :: SimplifiedExpr -> Text -> Bool
isPolynomialSv expr x = isMonomialSv expr x || case expr of
  Sum' terms -> all (`isMonomialSv` x) (NE.toList terms)
  _ -> False

isPositiveInteger :: Expr a -> Bool
isPositiveInteger (Number' n) = n > 1
isPositiveInteger _ = False

