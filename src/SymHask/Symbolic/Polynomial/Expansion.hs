-- |
-- Module: SymHask.Symbolic.Polynomial.Expansion
-- Description: Algebraic expansion of symbolic expressions
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
module SymHask.Symbolic.Polynomial.Expansion
    ( algebraicExpand
    , expandMainOp
    , rationalExpand
    ) where

import           Control.Monad.Error.Class            (MonadError (throwError))
import           Data.List.NonEmpty                   (NonEmpty ((:|)))
import qualified Data.List.NonEmpty                   as NE
import           Math.Combinatorics.Exact.Binomial    (choose)
import           SymHask.Symbolic
import           SymHask.Symbolic.Basic               (buildRestProduct,
                                                       buildRestSum)
import           SymHask.Symbolic.Polynomial.Rational (denom, numer,
                                                       rationalise)
import           SymHask.Symbolic.Simplification      ((.*.), (.+.), (./.))

-- $setup
-- >>> import SymHask.Symbolic

-- | Perform algebraic expansion on a symbolic expression, fully distributing
-- products over sums and expanding powers.
--
-- Expression \(u\) is in expanded form if @variables (u)@ does not contain a sum.
--
-- Also, each complete sub-expression of \(u\) and the denominator of each complete sub-expression
-- is in expanded form.
--
-- >>> let expr = ("x" + 2) * ("x" + 3) * ("x" + 4):: UnsimplifiedExpr
-- >>> fmap toHaskell $ simplify expr >>= algebraicExpand
-- Right "24 + 26 * x + 9 * x ^ 2 + x ^ 3"
--
-- >>> let expr = ("x" + 1)**(5/2):: UnsimplifiedExpr
-- >>> fmap toHaskell $ simplify expr >>= algebraicExpand
-- Right "(1 + x) ^ (1 / 2) + 2 * x * (1 + x) ^ (1 / 2) + x ^ 2 * (1 + x) ^ (1 / 2)"
algebraicExpand :: SimplifiedExpr -> EvalResult SimplifiedExpr
algebraicExpand u = do
  n <- numer u
  d <- denom u
  n' <- expandCore n
  d' <- expandCore d
  if d' == mkNumber 0
    then throwError DivisionByZero
    else
      if d' == mkNumber 1
        then pure n'
        else n' ./. d'

-- | Core structural expander used after numerator/denominator splitting.
-- This keeps the recursive expansion logic local to sums, products, powers,
-- and functions, while `algebraicExpand` handles quotient-like expressions by
-- splitting them first with `numer` and `denom`.
expandCore :: SimplifiedExpr -> EvalResult SimplifiedExpr
expandCore u = case u of
  Sum' (f :| []) -> pure f
  Sum' (f :| rest) -> do
    let first = f
    restSum <- buildRestSum rest
    left <- expandCore first
    right <- expandCore restSum
    left .+. right
  Product' (f :| []) -> pure f
  Product' (f :| rest) -> do
    let first = f
    restProd <- buildRestProduct rest
    r1 <- expandCore first
    r2 <- expandCore restProd
    expandProduct r1 r2
  Power' base (Number' n) | n >= 2 -> do
    b' <- expandCore base
    expandPower b' n
  Power' base (Fraction' num den)
    | num > 0 && den > 0 -> do
        b' <- expandCore base
        expandRationalPower b' num den
  Function' fname args -> do
    expandedArgs <- mapM expandCore (NE.toList args)
    case NE.nonEmpty expandedArgs of
      Just argList -> pure $ mkFunction fname argList
      Nothing      -> pure u
  _ -> pure u

-- | Helper to recursively expand products and powers formed during expansion.
-- We only recurse when the expression still contains a genuinely expandable
-- sum or a power with an expandable base. This avoids re-entering on stable
-- products like x*y, which would otherwise loop forever.
tryExpand :: SimplifiedExpr -> EvalResult SimplifiedExpr
tryExpand expr
  | needsFurtherExpansion expr = expandCore expr
  | otherwise = pure expr
 where
  needsFurtherExpansion :: SimplifiedExpr -> Bool
  needsFurtherExpansion = \case
    Sum' _ -> True
    Product' factors -> any needsFurtherExpansion (NE.toList factors)
    Power' base (Number' n) -> n > 1 && not (isAtomic base) && needsFurtherExpansion base
    UnaryDiff' x -> needsFurtherExpansion x
    BinaryDiff' x y -> needsFurtherExpansion x || needsFurtherExpansion y
    Factorial' x -> needsFurtherExpansion x
    Function' _ args -> any needsFurtherExpansion (NE.toList args)
    _ -> False

-- | Expand_product as in pseudocode: expand product of two expanded expressions.
-- After computing the product, recursively expand any newly formed structures.
expandProduct :: SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
expandProduct (Sum' (f :| rest)) s = do
  rRem <- buildRestSum rest
  left <- expandProduct f s
  right <- expandProduct rRem s
  left .+. right
expandProduct r s@(Sum' (_ :| _)) = expandProduct s r
expandProduct r s = do
  prod <- r .*. s
  -- Recursively expand if the result contains unexpanded products or powers
  tryExpand prod

-- | Expand_power: expand (u)^n where n >= 2 and u is expanded.
-- After expansion, recursively expand any newly formed structures.
expandPower :: SimplifiedExpr -> Integer -> EvalResult SimplifiedExpr
expandPower u n
  | n <= 0 = pure $ mkNumber 1
  | n == 1 = pure u
  | otherwise = case u of
      Sum' (f :| rest) -> do
        r <- buildRestSum rest
        -- binomial-like expansion via recursion
        let ks = [0 .. n]
        terms <- mapM (expandTerm f r n) ks
        case NE.nonEmpty terms of
          Nothing -> pure $ mkNumber 0
          Just tlist -> do
            result <- simplify $ mkSum tlist
            -- Recursively expand the result in case it contains unexpanded products/powers
            tryExpand result
      _ -> do
        result <- simplify $ mkPower u (mkNumber n)
        -- Recursively expand if result is a product or power that might need expansion
        tryExpand result
 where
  -- expand term for a given k: c * f^(n-k) * Expand_power(r,k)
  expandTerm f r n' k = do
    let c = choose n' k
    leftPow <- simplify $ mkPower f (mkNumber (n' - k))
    rightPow <- expandPower r k
    leftTerm <- mkNumber c .*. leftPow
    expandProduct leftTerm rightPow

-- | Expand a positive fractional power by splitting the exponent into its
-- integer part and fractional remainder:
--   u^(q + m) = u^m * u^q,  where  q = floor(f), m = f - floor(f).
expandRationalPower :: SimplifiedExpr -> Integer -> Integer -> EvalResult SimplifiedExpr
expandRationalPower u num den = do
  let (wholePart, remainder) = num `divMod` den
      fractionalPart = mkFraction remainder den

  wholeExpanded <-
    if wholePart <= 0
      then pure $ mkNumber 1
      else expandPower u wholePart

  if remainder == 0
    then pure wholeExpanded
    else do
      fractionalExpanded <- simplify $ mkPower u fractionalPart
      if wholeExpanded == mkNumber 1
        then pure fractionalExpanded
        else expandProduct fractionalExpanded wholeExpanded

-- | Transform an algebraic expression to rational-expanded form.
--
-- Steps:
--
-- 1. Rationalize the expression (bring to common denominators, etc.).
--
-- 2. Extract numerator and denominator with `numer` / `denom`.
--
-- 3. Algebraically expand numerator and denominator separately.
--
-- 4. Reassemble; if denominator expands to 0 return DivisionByZero.
--
-- A rational-expanded expression is rationalised and,
-- both numerator and denominator are in expanded form.
rationalExpand :: SimplifiedExpr -> EvalResult SimplifiedExpr
rationalExpand = go
 where
  go expr = do
    next <- rationalExpandOnce expr
    if next == expr
      then pure next
      else go next

  rationalExpandOnce u = do
    -- Step 1: rationalise the whole expression
    r <- rationalise u
    -- Step 2: extract numerator and denominator
    n <- numer r
    d <- denom r
    -- Step 3: expand numerator and denominator
    n' <- algebraicExpand n
    d' <- algebraicExpand d
    -- Step 4: check denominator and reassemble
    if d' == mkNumber 0
      then throwError DivisionByZero
      else
        if d' == mkNumber 1
          then pure n'
          else n' ./. d'

-- | Expand only the main operator of an expression.
--
-- This means the operator only expand the top-level structure of the expression,
-- without recursively expanding the operands of sums, products, or powers.
--
-- >>> let expr = "x" * (2 + (1 + "x")**2) :: UnsimplifiedExpr
-- >>> fmap toHaskell $ simplify expr >>= expandMainOp
-- Right "2 * x + x * (1 + x) ^ 2"
expandMainOp :: SimplifiedExpr -> EvalResult SimplifiedExpr
expandMainOp u@(Number' _) = pure u
expandMainOp u@(Fraction' _ _) = pure u
expandMainOp u@(Symbol' _) = pure u
expandMainOp u@(Sum' _) = pure u
expandMainOp (Product' factors) = expandMainProduct (NE.toList factors)
expandMainOp (Power' base (Number' n))
  | n >= 2 = expandMainPower base n
expandMainOp (Power' base (Fraction' num den))
  | num > 0 && den > 0 = expandMainRationalPower base num den
expandMainOp u = pure u

expandMainProduct :: [SimplifiedExpr] -> EvalResult SimplifiedExpr
expandMainProduct [] = pure $ mkNumber 1
expandMainProduct [x] = pure x
expandMainProduct [r, s] = expandMainProductPair r s
expandMainProduct (x : xs) = do
  rest <- expandMainProduct xs
  expandMainProductPair x rest

expandMainProductPair :: SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
expandMainProductPair (Sum' (f :| rest)) s = do
  r <- buildRestSum rest
  left <- expandMainProductPair f s
  right <- expandMainProductPair r s
  left .+. right
expandMainProductPair r (Sum' (f :| rest)) = do
  sRest <- buildRestSum rest
  left <- expandMainProductPair r f
  right <- expandMainProductPair r sRest
  left .+. right
expandMainProductPair r s = simplify $ mkProduct (r :| [s])

expandMainPower :: SimplifiedExpr -> Integer -> EvalResult SimplifiedExpr
expandMainPower u n
  | n <= 0 = pure $ mkNumber 1
  | n == 1 = pure u
  | otherwise = case u of
      Sum' (f :| rest) -> do
        r <- buildRestSum rest
        terms <- mapM (expandMainPowerTerm f r n) [0 .. n]
        case NE.nonEmpty terms of
          Nothing    -> pure $ mkNumber 0
          Just tlist -> simplify $ mkSum tlist
      _ -> simplify $ mkPower u (mkNumber n)

expandMainPowerTerm :: SimplifiedExpr -> SimplifiedExpr -> Integer -> Integer -> EvalResult SimplifiedExpr
expandMainPowerTerm f r n' k = do
  let c = choose n' k
  leftPow <- simplify $ mkPower f (mkNumber (n' - k))
  rightPow <- simplify $ mkPower r (mkNumber k)
  coeff <- mkNumber c .*. leftPow
  coeff .*. rightPow

expandMainRationalPower :: SimplifiedExpr -> Integer -> Integer -> EvalResult SimplifiedExpr
expandMainRationalPower u num den = do
  let (wholePart, remainder) = num `divMod` den
      fractionalPart = mkFraction remainder den

  wholeExpanded <-
    if wholePart <= 0
      then pure $ mkNumber 1
      else expandMainPower u wholePart

  if remainder == 0
    then pure wholeExpanded
    else do
      fractionalExpanded <- simplify $ mkPower u fractionalPart
      if wholeExpanded == mkNumber 1
        then pure fractionalExpanded
        else simplify $ mkProduct (fractionalExpanded :| [wholeExpanded])
