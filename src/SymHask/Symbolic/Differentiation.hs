{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PatternSynonyms #-}

module SymHask.Symbolic.Differentiation
    ( differentiate
    , pattern PartialD'
    , pattern UnevaluatedD'
    ) where

import           Control.Monad.Error.Class                               (throwError)
import qualified Data.List.NonEmpty                                      as NE
import           Data.Text                                               (Text)
import           SymHask.Symbolic
import           SymHask.Symbolic.Operators                              (freeOf)
import           SymHask.Symbolic.Simplification.AutomaticSimplification (automaticSimplify)

pattern UnevaluatedD' :: Expression -> Text -> Expression
pattern UnevaluatedD' u x = Function "D" [u, Symbol x]

pattern PartialD' :: Expression -> Text -> Integer -> Expression
pattern PartialD' f x i = Function "PartialD" [f, Symbol x, Number i]

-- | Let u be an algebraic expression and let x be a symbol. The operator
-- differentiate(u, x), which evaluates the derivative of u with respect to x
--
-- Note: All derivatives of trigonometric and hyperbolic functions are expressed in terms of
-- of sin and cos, and sinh and cosh respectively.
--
-- Note: This function does not perform full simplification of the result.
-- It only applies automatic simplification before and after differentiation.
-- More advanced simplification techniques may be needed to fully simplify the
-- result.
-- For example:
-- @toHaskell <$> differentiate (mkFunction "cot" ["x"]) "x"@ gives you
-- @Right "(-1) * (sin x) ^ (-2)"@
-- but @toHaskell <$> differentiate (cos "x" / sin "x") "x" @ gives you
-- @Right "(-1) + (-1) * (cos x) ^ 2 * (sin x) ^ (-2)"@
-- In fact, they are semantically equivalent, but the latter is not fully simplified.
differentiate :: Expression -> Text -> ExpressionResult Expression
differentiate u x = do
  u' <- automaticSimplify u
  d <- applyDifferentiationRule u' x
  automaticSimplify d

-- Quotient rule is not needed, it is simplfied to Product and Power
-- which are handled by differentiateProduct and differentiatePower respectively.
-- Assume u' is already simplified
applyDifferentiationRule :: Expression -> Text -> ExpressionResult Expression
applyDifferentiationRule u' x
  | u' == Symbol x = return 1
  | isPower u' = differentiatePower u' x
  | isSum u' = differentiateSum u' x
  | isProduct u' = differentiateProduct u' x
  | isFunction u' = differentiateFunction u' x
  | freeOf u' (Symbol x) = return 0
  | otherwise = return $ UnevaluatedD' u' x

-- Assume u' = (Power v w) is already simplified
differentiatePower :: Expression -> Text -> ExpressionResult Expression
differentiatePower (Power v w) x = do
  dv <- differentiate v x
  dw <- differentiate w x
  return $ w * v ** (w - 1) * dv + dw * v ** w * log v
differentiatePower u' _ = throwError $
  UnsupportedOperation "differentiatePower: not a power expression" u'

-- Assume u' = (Sum v w) is already simplified
differentiateSum :: Expression -> Text -> ExpressionResult Expression
differentiateSum (Sum terms) x = do
  -- Sum rule: (f₁ + f₂ + ... + fₙ)' = f₁' + f₂' + ... + fₙ'
  derivatives <- mapM (`differentiate` x) terms
  return $ Sum derivatives
differentiateSum u' _ = throwError $
  UnsupportedOperation "differentiateSum: not a sum expression" u'

-- Assume u' = (Product v w) is already simplified
differentiateProduct :: Expression -> Text -> ExpressionResult Expression
differentiateProduct u'@(Product factors) x = do
  let v = NE.head factors
  let w = u' / v
  dv <- differentiate v x
  dw <- differentiate w x
  return $ dv * w + v * dw
differentiateProduct u' _ = throwError $
  UnsupportedOperation "differentiateProduct: not a product expression" u'

-- | Assume u' = f(v) is already simplified
differentiateFunction :: Expression -> Text -> ExpressionResult Expression
differentiateFunction (Exp' v) x = do
  dv <- differentiate v x
  return $ exp v * dv
differentiateFunction (LogBase' b v) x = do
  dv <- differentiate v x
  db <- differentiate b x
  return $ dv / (v * log b) - db * log v / (b * log b ** 2)
differentiateFunction (Sin' v) x = do
  dv <- differentiate v x
  return $ cos v * dv
differentiateFunction (Cos' v) x = do
  dv <- differentiate v x
  return $ - (sin v * dv)
differentiateFunction (Tan' v) x = do
  dv <- differentiate v x
  return $ (1 / cos v) ** 2 * dv
differentiateFunction (Cot' v) x =do
  dv <- differentiate v x
  return $ - (((1 / sin v) ** 2) * dv)
differentiateFunction (Sec' v) x = do
  dv <- differentiate v x
  return (sin v / cos v ** 2 * dv)
differentiateFunction (Csc' v) x = do
  dv <- differentiate v x
  return $ - (cos v / sin v ** 2 * dv)
differentiateFunction (Asin' v) x = do
  dv <- differentiate v x
  return $ 1 / sqrt (1 - v ** 2) * dv
differentiateFunction (Acos' v) x = do
  dv <- differentiate v x
  return $ - ((1 / sqrt (1 - v ** 2)) * dv)
differentiateFunction (Atan' v) x = do
  dv <- differentiate v x
  return $ 1 / (1 + v ** 2) * dv
differentiateFunction (Acot' v) x = do
  dv <- differentiate v x
  return $ - ((1 / (1 + v ** 2)) * dv)
differentiateFunction (Asec' v) x = do
  dv <- differentiate v x
  return $ 1 / (abs v * sqrt (v ** 2 - 1)) * dv
differentiateFunction (Acsc' v) x = do
  dv <- differentiate v x
  return $ - ((1 / (abs v * sqrt (v ** 2 - 1))) * dv)
differentiateFunction (Sinh' v) x = do
  dv <- differentiate v x
  return $ cosh v * dv
differentiateFunction (Cosh' v) x = do
  dv <- differentiate v x
  return $ sinh v * dv
differentiateFunction (Tanh' v) x = do
  dv <- differentiate v x
  return $ 1 / cosh v ** 2 * dv
differentiateFunction (Coth' v) x = do
  dv <- differentiate v x
  return $ - ((1 / sinh v ** 2) * dv)
differentiateFunction (Sech' v) x = do
  dv <- differentiate v x
  return $ - ((sinh v / cosh v ** 2) * dv)
differentiateFunction (Csch' v) x = do
  dv <- differentiate v x
  return $ - ((cosh v / sinh v ** 2) * dv)
differentiateFunction (Asinh' v) x = do
  dv <- differentiate v x
  return $ 1 / sqrt (v ** 2 + 1) * dv
differentiateFunction (Acosh' v) x = do
  dv <- differentiate v x
  return $ 1 / sqrt (v ** 2 - 1) * dv
differentiateFunction (Atanh' v) x = do
  dv <- differentiate v x
  return $ 1 / (1 - v ** 2) * dv
differentiateFunction (ACoth' v) x = do
  dv <- differentiate v x
  return $ 1 / (1 - v ** 2) * dv
differentiateFunction (ASech' v) x = do
  dv <- differentiate v x
  return $ - ((1 / (v * sqrt (1 - v ** 2))) * dv)
differentiateFunction (ACsch' v) x = do
  dv <- differentiate v x
  return $ - ((1 / (abs v * sqrt (1 + v ** 2))) * dv)
differentiateFunction (Function fname args) x = do
  -- Generalized chain rule for undefined functions
  -- d/dx f(u₁, u₂, ..., uₙ) = Σᵢ (∂f/∂uᵢ) * (duᵢ/dx)
  chainTerms <- mapM (differentiateArgument fname args x) (NE.zip [1..] args)
  let nonZeroTerms = NE.filter (/= Number 0) chainTerms
  case nonZeroTerms of
    []     -> return $ Number 0
    [term] -> return term
    terms  -> return $ sum terms
  where
    differentiateArgument :: Text -> Operands -> Text -> (Integer, Expression) -> ExpressionResult Expression
    differentiateArgument funcName allArgs varName (argIndex, arg) = do
      argDerivative <- differentiate arg varName
      if argDerivative == Number 0
        then return $ Number 0
        else do
          let partialDeriv = PartialD' (Function funcName allArgs) varName argIndex
          return $ partialDeriv * argDerivative
differentiateFunction u' _ = throwError $
  UnsupportedOperation "differentiateFunction: not a function expression" u'
