{-# LANGUAGE ViewPatterns #-}

module SymHask.Symbolic.Basic.Absolute
    ( absExpr
    ) where

import           SymHask.Symbolic
import           SymHask.Symbolic.Basic.LinearForm (LinearForm (..), linearForm)
import           SymHask.Symbolic.Simplification

absExpr :: SimplifiedExpr -> EvalResult SimplifiedExpr
absExpr (Number' n) = pure $ mkNumber (abs n)
absExpr (Fraction' n d) = simplify $ mkFraction (abs n) (abs d)
absExpr (Product' factors) = mapM absExpr factors >>= simplify . mkProduct
absExpr (Power' b (Number' n)) = do
  absBase <- absExpr b
  absBase .**. mkNumber n
absExpr I' = pure $ mkNumber 1
absExpr (UnaryDiff' expr) = absExpr expr
absExpr (Quotient' n d) = do
  absN <- absExpr n
  absD <- absExpr d
  absN ./. absD
absExpr (Abs' inner) = absExpr inner
absExpr expr = do
  linear <- linearForm expr "i"
  case linear of
    Just (LinearForm (unsimplify -> imag) (unsimplify -> real)) ->
      if imag /= mkNumber 0 && real /= mkNumber 0
      -- abs(a + b*i) = sqrt(a^2 + b^2)
      then simplify $ (imag ** 2 + real ** 2) ** (1 / 2)
      else return $ Abs' expr
    Nothing -> return $ Abs' expr


