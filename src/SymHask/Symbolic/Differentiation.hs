{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PatternSynonyms #-}

module SymHask.Symbolic.Differentiation
    ( differentiate
    ) where

import           Control.Monad.Error.Class                               (throwError)
import qualified Data.List.NonEmpty                                      as NE
import           SymHask.Symbolic                                        (Expression (..),
                                                                          ExpressionError (..),
                                                                          ExpressionResult,
                                                                          isPower,
                                                                          isProduct,
                                                                          isSin,
                                                                          isSum,
                                                                          pattern Sin')
import           SymHask.Symbolic.Operators                              (freeOf)
import           SymHask.Symbolic.Simplification.AutomaticSimplification (automaticSimplify)
import Data.Text (Text)

pattern UnevaluatedD :: Expression -> Text -> Expression
pattern UnevaluatedD u x = Function "deriv" [u, Symbol x]


-- Let u be an algebraic expression and let x be a symbol. The operator
-- differentiate(u, x), which evaluates the derivative of u with respect to x
differentiate :: Expression -> Text -> ExpressionResult Expression
differentiate u x = do
  u' <- automaticSimplify u
  d <- applyDifferentiationRule u' x
  automaticSimplify d

applyDifferentiationRule :: Expression -> Text -> ExpressionResult Expression
applyDifferentiationRule u' x
  | u' == Symbol x = return 1
  | isPower u' = differentiatePower u' x
  | isSum u' = differentiateSum u' x
  | isProduct u' = differentiateProduct u' x
  | isSin u' = differentiateSin u' x
  | freeOf u' (Symbol x) = return 0
  | otherwise = return $ UnevaluatedD u' x

differentiatePower :: Expression -> Text -> ExpressionResult Expression
differentiatePower (Power v w) x = do
  dv <- differentiate v x
  dw <- differentiate w x
  return $ w * v ** (w - 1) * dv + dw * v ** w * log v
differentiatePower u' _ = throwError $
  UnsupportedOperation "differentiatePower: not a power expression" u'

differentiateSum :: Expression -> Text -> ExpressionResult Expression
differentiateSum u'@(Sum terms) x = do
  let v = NE.head terms
  let w = u' - v
  dv <- differentiate v x
  dw <- differentiate w x
  return $ dv + dw
differentiateSum u' _ = throwError $
  UnsupportedOperation "differentiateSum: not a sum expression" u'

differentiateProduct :: Expression -> Text -> ExpressionResult Expression
differentiateProduct u'@(Product factors) x = do
  let v = NE.head factors
  let w = u' / v
  dv <- differentiate v x
  dw <- differentiate w x
  return $ dv * w + v * dw
differentiateProduct u' _ = throwError $
  UnsupportedOperation "differentiateProduct: not a product expression" u'

differentiateSin :: Expression -> Text -> ExpressionResult Expression
differentiateSin (Sin' v) x = do
  dv <- differentiate v x
  return $ cos v * dv
differentiateSin u' _ = throwError $
  UnsupportedOperation "differentiateSin: not a sine expression" u'
