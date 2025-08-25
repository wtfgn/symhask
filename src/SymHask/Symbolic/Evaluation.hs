{-# LANGUAGE OverloadedLists #-}

module SymHask.Symbolic.Evaluation
    ( toFunctionSafe
    ) where

import           Control.Monad              (foldM)
import           Data.Ratio                 ((%))
import           Data.Text                  (Text)
import           SymHask.Symbolic           (Expression (..),
                                             ExpressionResult (..),
                                             getBinaryFunction,
                                             getUnaryFunction)
import           SymHask.Symbolic.Factorial (safeFactorial)

-- ============================================================================
-- * Types and Type Aliases
-- ============================================================================

-- | Type alias for variable mapping functions
type VariableMap a b = Text -> (a -> b)


-- ============================================================================
-- * Main Conversion Functions
-- ============================================================================

toFunctionSafe
  :: (Floating b, RealFrac b)
  => Expression
  -> VariableMap a b
  -> (a -> ExpressionResult b)
toFunctionSafe expr varMap = case expr of
  Number n ->
    const . pure $ fromIntegral n

  Fraction n d ->
    const . pure $ fromRational (n % d)

  Symbol s ->
    pure . varMap s

  Product xs ->
    \v -> foldM (\acc x -> (*) acc <$> toFunctionSafe x varMap v) 1 xs

  Sum xs ->
    \v -> foldM (\acc x -> (+) acc <$> toFunctionSafe x varMap v) 0 xs

  Quotient n d ->
    \v -> (/) <$> toFunctionSafe n varMap v <*> toFunctionSafe d varMap v

  UnaryDifference x ->
    fmap negate . toFunctionSafe x varMap

  BinaryDifference x y ->
    \v -> (-) <$> toFunctionSafe x varMap v <*> toFunctionSafe y varMap v

  Power x y ->
    \v -> (**) <$> toFunctionSafe x varMap v <*> toFunctionSafe y varMap v

  Factorial x ->
    \v -> do
      xVal <- toFunctionSafe x varMap v
      safeFactorial xVal

  e@(Function _ [x]) ->
    case getUnaryFunction e of
      Just f -> fmap f . toFunctionSafe x varMap
      Nothing -> const $ ExpressionError "Unknown unary function"

  e@(Function _ [x, y]) ->
    case getBinaryFunction e of
      Just f -> \v -> f <$> toFunctionSafe x varMap v <*> toFunctionSafe y varMap v
      Nothing -> const $ ExpressionError "Unknown binary function"

  Function _ _ ->
    const $ ExpressionError "Unsupported function arity"
