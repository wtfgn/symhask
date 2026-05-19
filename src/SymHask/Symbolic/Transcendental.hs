{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module SymHask.Symbolic.Transcendental
  ( expandExp,
    expandTrig,
    contractExp,
    trigSubs,
  )
where

import Control.Monad.Error.Class (throwError)
import Data.List.NonEmpty (NonEmpty ((:|)))
import SymHask.Symbolic
import SymHask.Symbolic.Basic (mapOperands, isZero)
import SymHask.Symbolic.Basic.Polynomial (algebraicExpand, denom, expandMainOp)
import SymHask.Symbolic.Basic.Utils (buildRestProduct, buildRestSum)
import SymHask.Symbolic.Simplification ( (.+.), (.-.), (.**.), (.*.))
import Control.Monad (when, foldM)
import qualified Data.List.NonEmpty as NE


-- | Expand expressions in the exponential sense.
--
-- The algorithm recursively expands subexpressions, then applies the
-- exponential rules to any exp(...) node:
--   exp(u + v) = exp(u) * exp(v)
--   exp(w * u) = exp(u) ^ w  when w is an integer
--
-- Before the exp rules are applied, the argument is algebraically expanded.
-- This lets expressions such as exp((x+y)(x-y)) reduce to exp(x^2) / exp(y^2).
-- If a denominator simplifies to 0 during the process, DivisionByZero is raised.

expandExp :: SimplifiedExpr -> Either ExprError SimplifiedExpr
expandExp expr = do
  d <- denom expr >>= expandExpCore
  when (isZero d) $ throwError DivisionByZero
  expandExpCore expr

expandExpCore :: SimplifiedExpr -> EvalResult SimplifiedExpr
expandExpCore u@(Number' _) = pure u
expandExpCore u@(Fraction' _ _) = pure u
expandExpCore u@(Symbol' _) = pure u
expandExpCore (Exp' x) =
  expandExpCore x >>= expandExpRules
expandExpCore u = mapOperands expandExpCore u

expandExpRules :: SimplifiedExpr -> EvalResult SimplifiedExpr
expandExpRules a = do
  a' <- algebraicExpand a
  case a' of
    Sum' (f :| rest) -> do
      r <- buildRestSum rest
      left <- expandExpRules f
      right <- expandExpRules r
      left .*. right
    Product' (f :| rest) -> do
      rest' <- buildRestProduct rest
      s <- expandExpRules rest'
      if isNumber f
        then s .**. f
        else return $ Exp' a'
    _ -> pure $ Exp' a'

data TrigKind
  = TrigSin
  | TrigCos

-- | Expand trigonometric functions sin/cos according to angle addition and multiple angle identities.
-- For non-sin/cos trig functions, use 'trigSubs' first to rewrite them in terms of sin/cos.
expandTrig :: SimplifiedExpr -> EvalResult SimplifiedExpr
expandTrig expr = do
  d <- denom expr >>= expandTrigCore
  when (isZero d) $ throwError DivisionByZero
  expandTrigCore expr >>= algebraicExpand

expandTrigCore :: SimplifiedExpr -> EvalResult SimplifiedExpr
expandTrigCore u@(Number' _) = pure u
expandTrigCore u@(Fraction' _ _) = pure u
expandTrigCore u@(Symbol' _) = pure u
expandTrigCore (Sin' x) = expandTrigCore x >>= expandTrigRules TrigSin
expandTrigCore (Cos' x) = expandTrigCore x >>= expandTrigRules TrigCos
expandTrigCore u = mapOperands expandTrigCore u

expandTrigRules :: TrigKind -> SimplifiedExpr -> EvalResult SimplifiedExpr
expandTrigRules kind arg = do
  arg' <- algebraicExpand arg
  case arg' of
    Sum' (f :| rest) -> do
      r <- buildRestSum rest
      expandTrigSum kind f r
    Product' (Number' n :| rest) -> do
      theta <- buildRestProduct rest
      expandTrigMultiple kind n theta
    _ -> pure $ mkTrig kind arg

expandTrigSum :: TrigKind -> SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
expandTrigSum TrigSin u v = do
  su <- expandTrigRules TrigSin u
  cu <- expandTrigRules TrigCos u
  sv <- expandTrigRules TrigSin v
  cv <- expandTrigRules TrigCos v
  left <- su .*. cv
  right <- cu .*. sv
  left .+. right
expandTrigSum TrigCos u v = do
  cu <- expandTrigRules TrigCos u
  cv <- expandTrigRules TrigCos v
  su <- expandTrigRules TrigSin u
  sv <- expandTrigRules TrigSin v
  left <- cu .*. cv
  right <- su .*. sv
  left .-. right

expandTrigMultiple :: TrigKind -> Integer -> SimplifiedExpr -> EvalResult SimplifiedExpr
expandTrigMultiple kind n theta
  | n == 0 = pure $ case kind of
      TrigSin -> mkNumber 0
      TrigCos -> mkNumber 1
  | n < 0 = do
      expanded <- expandTrigMultiple kind (-n) theta
      case kind of
        TrigSin -> simplify $ mkUnaryDiff expanded
        TrigCos -> pure expanded
  | n == 1 = expandTrigRules kind theta
   | otherwise = do
       -- Use the angle addition identity to reduce n recursively:
       -- sin(nθ) = sin((n-1)θ + θ) = sin((n-1)θ)*cos(θ) + cos((n-1)θ)*sin(θ)
       -- cos(nθ) = cos((n-1)θ + θ) = cos((n-1)θ)*cos(θ) - sin((n-1)θ)*sin(θ)
       su <- expandTrigMultiple TrigSin (n - 1) theta
       cu <- expandTrigMultiple TrigCos (n - 1) theta
       sv <- expandTrigRules TrigSin theta
       cv <- expandTrigRules TrigCos theta
       case kind of
         TrigSin -> do
           left <- su .*. cv
           right <- cu .*. sv
           left .+. right
         TrigCos -> do
           left <- cu .*. cv
           right <- su .*. sv
           left .-. right

mkTrig :: TrigKind -> SimplifiedExpr -> SimplifiedExpr
mkTrig TrigSin = Sin'
mkTrig TrigCos = Cos'


-- | Contract exponential expressions by combining products of exponentials and
-- rewriting powers of exponentials into a single exponential.
contractExp :: SimplifiedExpr -> EvalResult SimplifiedExpr
contractExp u@(Number' _) = pure u
contractExp u@(Fraction' _ _) = pure u
contractExp u@(Symbol' _) = pure u
contractExp u = mapOperands contractExp u >>= contractExpRules

contractExpRules :: SimplifiedExpr -> EvalResult SimplifiedExpr
contractExpRules u = do
  v <- expandMainOp u
  case v of
    Power' (Exp' x) s -> do
      p <- x .*. s
      contracted <- if needsFurtherContraction p then contractExpRules p else return p
      pure $ Exp' contracted
    Product' factors -> do
      (p, s) <- foldM combineExpFactors (mkNumber 1, mkNumber 0) factors
      if isZero s then return v else Exp' s .*. p
    Sum' terms -> foldM combineExpTerms (mkNumber 0) terms
    _ -> pure v
  where
    needsFurtherContraction expr = isProduct expr || isPower expr

    combineExpFactors (p, s) factor = case factor of
      Exp' n -> do
        s' <- s .+. n
        return (p, s')
      _ -> do
        p' <- p .*. factor
        return (p', s)

    combineExpTerms acc term
      | isProduct term || isPower term = contractExpRules term >>= (acc .+.)
      | otherwise = acc .+. term

-- | Substitute trigonometric functions tan/cot/sec/csc with sin/cos representations.
--
-- tan(u) = sin(u) / cos(u)
-- cot(u) = cos(u) / sin(u)
-- sec(u) = 1 / cos(u)
-- csc(u) = 1 / sin(u)
trigSubs :: SimplifiedExpr -> EvalResult SimplifiedExpr
trigSubs u@(Number' _) = pure u
trigSubs u@(Fraction' _ _) = pure u
trigSubs u@(Symbol' _) = pure u
trigSubs (Tan' x) = do
  x' <- trigSubs x
  let sinx = mkFunction "sin" (x' :| [])
      cosx = mkFunction "cos" (x' :| [])
  simplify $ mkQuotient sinx cosx
trigSubs (Cot' x) = do
  x' <- trigSubs x
  let sinx = mkFunction "sin" (x' :| [])
      cosx = mkFunction "cos" (x' :| [])
  simplify $ mkQuotient cosx sinx
trigSubs (Sec' x) = do
  x' <- trigSubs x
  let cosx = mkFunction "cos" (x' :| [])
  simplify $ mkQuotient (mkNumber 1) cosx
trigSubs (Csc' x) = do
  x' <- trigSubs x
  let sinx = mkFunction "sin" (x' :| [])
  simplify $ mkQuotient (mkNumber 1) sinx
trigSubs u = mapOperands trigSubs u
