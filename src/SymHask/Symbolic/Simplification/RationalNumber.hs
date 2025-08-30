{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE OverloadedLists #-}

module SymHask.Symbolic.Simplification.RationalNumber
    ( simplifyRNE
    , simplifyRationalNumber
    ) where

import           SymHask.Symbolic (Expression (..), ExpressionError (..),
                                   ExpressionResult, mkFraction)
import Control.Monad.Error.Class (throwError)

-- This module is intended to handle simplification of rational numbers
-- and related operations on symbolic expressions involving rational numbers.

-- ============================================================================
-- * Simplification Functions
-- ============================================================================

simplifyRationalNumber :: Expression -> ExpressionResult Expression
simplifyRationalNumber = \case
  u@(Number _) -> return u

  u@(Fraction n d)
    | d == 0 -> throwError $ DivisionByZero u
    | n == 0 -> return 0
    | n `mod` d == 0 -> return (Number (n `div` d))
    | otherwise ->
      let
        g = gcd n d
        n' = if d > 0 then n `div` g else (-n) `div` g
        d' = if d > 0 then d `div` g else (-d) `div` g
      in return (Fraction n' d')
  u -> throwError $ UnsupportedOperation
    "Unsupported expression type for rational simplification, only \
    \a fraction in function (FracOp) notation (with non-zero denominator) \
    \or an integer is expected." u

simplifyRNE :: Expression -> ExpressionResult Expression
simplifyRNE expr = do
  simplified <- simplifyStep expr
  simplifyRationalNumber simplified

simplifyStep :: Expression -> ExpressionResult Expression
simplifyStep = \case
  u@(Number _) -> return u

  u@(Fraction _ d)
    | d == 0 -> throwError $ DivisionByZero u
    | otherwise -> simplifyRationalNumber u

  Sum [x] -> simplifyStep x

  Sum [x, y] -> do
    x' <- simplifyStep x
    y' <- simplifyStep y
    evaluateSum x' y'

  UnaryDifference x -> do
    x' <- simplifyStep x
    evaluateProduct (Number (-1)) x'

  BinaryDifference x y -> do
    x' <- simplifyStep x
    y' <- simplifyStep y
    evaluateDifference x' y'

  Product [x] -> simplifyStep x

  Product [x, y] -> do
    x' <- simplifyStep x
    y' <- simplifyStep y
    evaluateProduct x' y'

  Quotient x y -> do
    x' <- simplifyStep x
    y' <- simplifyStep y
    evaluateQuotient x' y'

  Power x (Number n) -> do
    x' <- simplifyStep x
    evaluatePower x' n

  u -> throwError $ UnsupportedOperation
    "Unsupported expression type for simplification, \
    \only RNE is expected." u


-- ============================================================================
-- * Evaluation Helper Functions
-- ============================================================================
evaluateSum :: Expression -> Expression -> ExpressionResult Expression
evaluateSum v w = do
  nv <- safeGetNumerator v
  nw <- safeGetNumerator w
  dv <- safeGetDenominator v
  dw <- safeGetDenominator w

  let commonDenominator = dv * dw
      newNumerator = nv * dw + nw * dv

  return $ Fraction newNumerator commonDenominator

evaluateDifference :: Expression -> Expression -> ExpressionResult Expression
evaluateDifference v w = do
  nv <- safeGetNumerator v
  nw <- safeGetNumerator w
  dv <- safeGetDenominator v
  dw <- safeGetDenominator w

  let commonDenominator = dv * dw
      newNumerator = nv * dw - nw * dv

  return $ Fraction newNumerator commonDenominator

evaluateProduct :: Expression -> Expression -> ExpressionResult Expression
evaluateProduct v w = do
  nv <- safeGetNumerator v
  nw <- safeGetNumerator w
  dv <- safeGetDenominator v
  dw <- safeGetDenominator w

  let newNumerator = nv * nw
      newDenominator = dv * dw

  return $ Fraction newNumerator newDenominator

evaluateQuotient :: Expression -> Expression -> ExpressionResult Expression
evaluateQuotient v w = do
  nv <- safeGetNumerator v
  nw <- safeGetNumerator w
  dv <- safeGetDenominator v
  dw <- safeGetDenominator w

  if nw == 0
    then throwError $ DivisionByZero w
    else let newNumerator = nv * dw
             newDenominator = dv * nw
         in return $ Fraction newNumerator newDenominator

evaluatePower :: Expression -> Integer -> ExpressionResult Expression
evaluatePower v n = do
  let u = Power v (Number n)
  vn <- safeGetNumerator v
  vd <- safeGetDenominator v

  if
    | vn == 0 && n >= 1 -> return 0
    | vn == 0 && n <= 0 -> throwError $ InvalidDomain "Zero to non-positive power" u
    | n > 0             -> evaluatePower v (n - 1) >>= \s -> evaluateProduct s v
    | n == 0            -> return 1
    | n == -1           -> return $ mkFraction vd vn
    | n < -1            -> evaluatePower (mkFraction vd vn) (-n)
    | otherwise         -> throwError $ EvaluationFailure "Invalid power operation" u

-- ============================================================================
-- * Accessor Functions
-- ============================================================================

getNumerator :: Expression -> Maybe Integer
getNumerator (Number n)     = Just n
getNumerator (Fraction n _) = Just n
getNumerator _              = Nothing

getDenominator :: Expression -> Maybe Integer
getDenominator (Number _)     = Just 1
getDenominator (Fraction _ d) = Just d
getDenominator _              = Nothing

-- ============================================================================
-- * Safe Accessor Functions
-- ============================================================================

safeGetNumerator :: Expression -> ExpressionResult Integer
safeGetNumerator expr =
  case getNumerator expr of
    Just n -> return n
    Nothing -> throwError $
      UnsupportedOperation "Cannot extract numerator from non-numeric expression" expr

safeGetDenominator :: Expression -> ExpressionResult Integer
safeGetDenominator expr =
  case getDenominator expr of
    Just d -> if d == 0
              then throwError $ DivisionByZero expr
              else return d
    Nothing -> throwError $
      UnsupportedOperation "Cannot extract denominator from non-numeric expression" expr
