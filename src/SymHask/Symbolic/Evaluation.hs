{-# LANGUAGE OverloadedLists #-}

module SymHask.Symbolic.Evaluation
    ( toFunctionSafe
    ) where

import           Control.Monad              (foldM)
import           Control.Monad.Error.Class  (MonadError (throwError))
import           Data.Ratio                 ((%))
import           Data.Text                  (Text)
import           SymHask.Symbolic           (Expression (..),
                                             ExpressionError (..),
                                             ExpressionResult,
                                             getBinaryFunction,
                                             getUnaryFunction)
import           SymHask.Symbolic.Factorial (factorial)

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
    const . return $ fromIntegral n

  Fraction n d ->
    const . return $ fromRational (n % d)

  Symbol s ->
    return . varMap s

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

  u@(Factorial x) ->
    \v -> do
      xVal <- toFunctionSafe x varMap v
      let
        rounded = round xVal
        tolerance = 1e-12  -- Small tolerance for floating-point comparison
      -- Validate that the input is actually an integer
      if abs (fromIntegral rounded - xVal) > tolerance
        then throwError $ InvalidDomain "factorial requires integer input" u
        else if rounded < 0
          then throwError $ InvalidDomain "factorial of negative number" u
        else return $ fromIntegral (factorial rounded)

  u@(Function _ [x]) ->
    case getUnaryFunction u of
      Just f -> fmap f . toFunctionSafe x varMap
      Nothing -> const $ throwError $
        UnsupportedOperation "Unknown unary function" u

  u@(Function _ [x, y]) ->
    case getBinaryFunction u of
      Just f -> \v -> f <$> toFunctionSafe x varMap v <*> toFunctionSafe y varMap v
      Nothing -> const $ throwError $
        UnsupportedOperation "Unknown binary function" u

  u@(Function _ _) ->
    const $ throwError $
      UnsupportedOperation "Unsupported function arity" u
