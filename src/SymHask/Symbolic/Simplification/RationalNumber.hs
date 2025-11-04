{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE OverloadedLists       #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module SymHask.Symbolic.Simplification.RationalNumber
    ( simplifyRNE
    , toStandardRNE
    ) where

import           Control.Monad                ((>=>))
import           Control.Monad.Error.Class    (throwError)
import           Data.Coerce                  (coerce)
import           SymHask.Symbolic

simplifyRNE :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
simplifyRNE = simplifyRNEStep >=> toStandardRNE

toStandardRNE :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
toStandardRNE = \case
  Number' n -> pure $ mkNumber n
  Fraction' n d
    | d == 0 -> throwError DivisionByZero
    | n == 0 -> pure $ mkNumber 0
    | n `mod` d == 0 -> pure $ mkNumber (n `div` d)
    | otherwise ->
      let
        g = gcd n d
        n' = if d > 0 then n `div` g else (-n) `div` g
        d' = if d > 0 then d `div` g else (-d) `div` g
      in pure $ coerce (mkFraction n' d')

  _ -> throwError $ UnsupportedOperation
    "toStandardRNE only supports Number and Fraction types."

simplifyRNEStep :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
simplifyRNEStep = \case
  Number' n -> pure $ mkNumber n

  Fraction' n d
    | d == 0 -> throwError DivisionByZero
    | otherwise -> coerce $ toStandardRNE (mkFraction n d)

  Sum' [x] -> simplifyRNEStep x

  Sum' [x, y] -> do
    x' <- simplifyRNEStep x
    y' <- simplifyRNEStep y
    evaluateSum x' y'

  UnaryDiff' x -> do
    x' <- simplifyRNEStep x
    evaluateProduct (mkNumber (-1)) x'

  BinaryDiff' x y -> do
    x' <- simplifyRNEStep x
    y' <- simplifyRNEStep y
    evaluateDifference x' y'

  Product' [x] -> simplifyRNEStep x

  Product' [x, y] -> do
    x' <- simplifyRNEStep x
    y' <- simplifyRNEStep y
    evaluateProduct x' y'

  Quotient' x y -> do
    x' <- simplifyRNEStep x
    y' <- simplifyRNEStep y
    evaluateQuotient x' y'


  Power' x (Number' n) -> do
    x' <- simplifyRNEStep x
    evaluatePower x' n

  _ -> throwError $ UnsupportedOperation
    "Only integer, fraction, unary/binary sums, unary/binary differences, \
    \unary/binary products, quotients, powers (with integer exponents), \
    \are supported."

evaluateSum :: UnsimplifiedExpr -> UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
evaluateSum v w = do
  nv <- getNumerator v
  dv <- getDenominator v
  nw <- getNumerator w
  dw <- getDenominator w
  let n = nv * dw + nw * dv
  let d = dv * dw
  return $ mkFraction n d

evaluateDifference :: UnsimplifiedExpr -> UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
evaluateDifference v w = do
  nv <- getNumerator v
  dv <- getDenominator v
  nw <- getNumerator w
  dw <- getDenominator w
  let n = nv * dw - nw * dv
  let d = dv * dw
  return $ mkFraction n d

evaluateProduct :: UnsimplifiedExpr -> UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
evaluateProduct v w = do
  nv <- getNumerator v
  dv <- getDenominator v
  nw <- getNumerator w
  dw <- getDenominator w
  let n = nv * nw
  let d = dv * dw
  return $ mkFraction n d

evaluateQuotient :: UnsimplifiedExpr -> UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
evaluateQuotient v w = do
  nv <- getNumerator v
  dv <- getDenominator v
  nw <- getNumerator w
  dw <- getDenominator w
  if nw == 0
    then throwError DivisionByZero
    else return $ mkFraction (nv * dw) (dv * nw)

evaluatePower :: UnsimplifiedExpr -> Integer -> EvalResult UnsimplifiedExpr
evaluatePower v n = do
  nv <- getNumerator v
  dv <- getDenominator v
  if
    | nv == 0 && n  >= 1 -> return $ mkNumber 0
    | nv == 0 && n <= 0  -> throwError DivisionByZero
    | n > 0 -> evaluatePower v (n - 1) >>= \s -> evaluateProduct s v
    | n == 0 -> return $ mkNumber 1
    | n == -1 -> return $ mkFraction dv nv
    | n < -1 -> evaluatePower (mkFraction dv nv) (-n)
    | otherwise -> throwError $ EvaluationFailure
        "Unexpected case in power evaluation."

getNumerator :: UnsimplifiedExpr -> EvalResult Integer
getNumerator (Number' n)     = pure n
getNumerator (Fraction' n _) = pure n
getNumerator _              = throwError $ UnsupportedOperation
  "Only Number and Fraction types are supported."

getDenominator :: UnsimplifiedExpr -> EvalResult Integer
getDenominator (Number' _)     = return 1
getDenominator (Fraction' _ d) = return d
getDenominator _              = throwError $ UnsupportedOperation
  "Only Number and Fraction types are supported."
