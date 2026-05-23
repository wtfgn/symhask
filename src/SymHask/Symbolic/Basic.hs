{-# LANGUAGE MultiWayIf   #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module: SymHask.Symbolic.Basic
-- Description: Basic symbolic expression analysis and utilities
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
--
-- Supports basic analysis of symbolic expressions,
-- including function parity, linear form detection, free-of checks, and substitution.
module SymHask.Symbolic.Basic
    ( -- * Analysis
      FunctionParity (..)
    , LinearForm (..)
    , completeSubExprs
    , evenOdd
    , linearForm
    , separateFactors
      -- * Free-of checks
    , freeOf
    , setFreeOf
      -- ** Complexity
    , treeSize
      -- ** Operand analysis
    , exponents
    , operands
    , symbols
      -- * Substitution
    , Substitution.Pattern (..)
    , Substitution.Replacement (..)
    , concurSubs
    , seqSubs
    , subs
      -- * Evaluation
    , evalAbs
    , evalMax
      -- * Utilities
    , buildRestProduct
    , buildRestSum
    , isZero
    , mapOperands
    ) where

import           Control.Monad
import           Control.Monad.Error.Class           (throwError)
import qualified Data.HashSet                        as HS
import qualified Data.List.NonEmpty                  as NE
import           Data.Text                           (Text)
import           SymHask.Printer
import           SymHask.Symbolic
import qualified SymHask.Symbolic.Basic.Substitution as Substitution
import           SymHask.Symbolic.Simplification

-- | Classification of a function as even, odd, or neither with
-- respect to a variable.
data FunctionParity
  = EvenFunc
  | OddFunc
  | NeitherFunc
  deriving (Eq, Show)

-- | A linear form represented as \(ax + b\),
-- where `coeffTerm` is \(a\) and `constTerm` is \(b\).
data LinearForm
  = LinearForm
      { coeffTerm :: SimplifiedExpr
        -- ^ Coefficient of x
      , constTerm :: SimplifiedExpr
        -- ^ Constant term
      }
  deriving (Eq, Show)

-- | Return the size of the expression tree, defined as the total number of nodes in the expression.
-- The data constructor counts as 1, and the size of the children are added to it. For example:
--
-- >>> treeSize $ ("x"**2 + "y" :: UnsimplifiedExpr)
-- 5
-- Note that for the same mathematical expression, the simplified and unsimplified forms
-- may have different tree sizes. For example:
--
-- >>> let unsimplified = "x" + "x" + "x" :: UnsimplifiedExpr
-- >>> let simplified = simplify unsimplified
-- >>> treeSize unsimplified
-- >>> treeSize <$> simplified
-- 5
-- Right 3
--
-- This is a measure of the complexity of the expression
-- and can be used to compare different expressions.
treeSize :: Expr a -> Int
treeSize = \case
  Number' _ -> 1
  Fraction' _ _ -> 3
  Symbol' _ -> 1
  Quotient' n d -> 1 + treeSize n + treeSize d
  UnaryDiff' x -> 1 + treeSize x
  BinaryDiff' x y -> 1 + treeSize x + treeSize y
  Product' factors -> 1 + sum (NE.map treeSize factors)
  Sum' terms -> 1 + sum (NE.map treeSize terms)
  Power' b e -> 1 + treeSize b + treeSize e
  Factorial' expr -> 1 + treeSize expr
  Function' _ args -> 1 + sum (NE.map treeSize args)

-- | Collect all subexpressions of a given expression, including the expression itself.
--
-- For example, for the expression "x"**2 + "y", the subexpressions would include:
--
-- >>> let expr = "x"**2 + "y" :: UnsimplifiedExpr
-- >>> HS.map toHaskell <$> completeSubExprs <$> simplify expr
-- Right (fromList ["x ^ 2 + y","y","x ^ 2","x","2"])
completeSubExprs :: SimplifiedExpr -> HS.HashSet SimplifiedExpr
completeSubExprs expr
  | null (operands expr) = HS.singleton expr
  | otherwise = HS.insert expr (HS.unions subSets)
 where
  subSets = map completeSubExprs $ operands expr



-- | Separate factors into parts free of variable x and parts dependent on x
-- For expression \(u\,v\,w\dots\), separates into (free_part, dependent_part) where:
-- - free_part contains factors that don't depend on \(x\)
-- - dependent_part contains factors that do depend on \(x\)
type Dependent = SimplifiedExpr
type Free = SimplifiedExpr
separateFactors :: SimplifiedExpr -> SimplifiedExpr -> EvalResult (Free, Dependent)
separateFactors (Product' factors) var =
  foldM processFactor (mkNumber 1, mkNumber 1) (NE.toList factors)
 where
  -- Process a single factor
  processFactor ::
    (SimplifiedExpr, SimplifiedExpr) ->
    SimplifiedExpr ->
    EvalResult (SimplifiedExpr, SimplifiedExpr)
  processFactor (currFree, currDep) factor = do
    -- if freeOf(f, x) then
    if freeOf factor var
      then do
        -- free_of_part := f * free_of_part
        newFree <- factor .*. currFree
        return (newFree, currDep)
      else do
        -- dependent_part := f * dependent_part
        newDependent <- factor .*. currDep
        return (currFree, newDependent)
-- Handle non-product expressions
separateFactors expr var = do
  -- if freeOf(u, x) then (u, 1)
  if freeOf expr var
    then return (expr, mkNumber 1)
    -- else (1, u)
    else return (mkNumber 1, expr)

-- | Determine if a function is even, odd, or neither with respect to a variable.
-- A function \(f(x)\) is even if \(f(-x) = f(x)\) for all \(x\), odd if \(f(-x) = -f(x)\) for all \(x\), and neither otherwise.
evenOdd :: SimplifiedExpr -> Text -> EvalResult FunctionParity
evenOdd expr x = do
  negX <- simplify (negate (mkSymbol x) :: UnsimplifiedExpr)
  substituted <-
    subs
      ( Substitution.Pattern (mkSymbol x)
      ,Substitution.Replacement negX )
      expr
  if
    | expr .-. substituted == pure (mkNumber 0) -> return EvenFunc
    | expr .+. substituted == pure (mkNumber 0) -> return OddFunc
    | otherwise                                 -> return NeitherFunc

-- | Evaluate the absolute value of an expression, simplifying where possible.
evalAbs :: SimplifiedExpr -> EvalResult SimplifiedExpr
evalAbs (Number' n) = pure $ mkNumber (abs n)
evalAbs (Fraction' n d) = simplify $ mkFraction (abs n) (abs d)
evalAbs (Product' factors) = mapM evalAbs factors >>= simplify . mkProduct
evalAbs (Power' b (Number' n)) = do
  absBase <- evalAbs b
  absBase .**. mkNumber n
evalAbs I' = pure $ mkNumber 1
evalAbs (UnaryDiff' expr) = evalAbs expr
evalAbs (Quotient' n d) = do
  absN <- evalAbs n
  absD <- evalAbs d
  absN ./. absD
evalAbs (Abs' inner) = evalAbs inner
evalAbs expr = do
  linear <- linearForm expr "i"
  case linear of
    Just (LinearForm (unsimplify -> imag) (unsimplify -> real)) ->
      if imag /= mkNumber 0 && real /= mkNumber 0
        -- abs(a + b*i) = sqrt(a^2 + b^2)
        then simplify $ (imag ** 2 + real ** 2) ** (1 / 2)
        else return $ Abs' expr
    Nothing -> return $ Abs' expr

-- | Evaluate the maximum of a set of expressions, simplifying where possible.
evalMax :: HS.HashSet SimplifiedExpr -> EvalResult SimplifiedExpr
evalMax exprSet = case HS.toList exprSet of
  [] -> throwError $ UnsupportedOperation "evalMax: empty set"
  [Max' xs] -> evalMax xs -- Flatten nested max
  [x] -> return x
  xs -> do
    flattened <- flattenMax xs
    let survivors = eliminateComparable flattened
    case survivors of
      [] ->
        throwError $
          UnsupportedOperation "evalMax: no survivors after elimination"
      [x] -> return x
      _ -> return $ mkMax (HS.fromList survivors)
 where
  -- Eliminate expressions that are definitely less than others
  eliminateComparable :: [SimplifiedExpr] -> [SimplifiedExpr]
  eliminateComparable = eliminateBy isDefinitelyGreaterThan

    {- | Generic elimination: keep elements that are not dominated by any other.
    `d x y` should be True when x dominates y (i.e. x > y).
    Order of survivors is preserved.
  -}
  eliminateBy :: (a -> a -> Bool) -> [a] -> [a]
  eliminateBy _ [] = []
  eliminateBy _ [x] = [x]
  eliminateBy d (x : xs)
    | any (`d` x) xs = eliminateBy d xs
    | otherwise = x : eliminateBy d (filter (not . d x) xs)

  -- -- Flatten nested Max expressions into a single list
  -- -- Max({3, Max({2, x})}) becomes [3, 2, x]
  flattenMax :: [SimplifiedExpr] -> EvalResult [SimplifiedExpr]
  flattenMax = flattenM $ \case
    Max' innerExprs -> pure $ Just (HS.toList innerExprs)
    _ -> pure Nothing

    {- | Monadic flattener.
    Given a function that optionally returns a list of inner elements to splice,
    recursively flattens those inner lists.

    Example usage:
      flattenM (\case Max' inner -> pure $ Just (HS.toList inner); _ -> pure Nothing) xs
  -}
  flattenM :: (Monad m) => (a -> m (Maybe [a])) -> [a] -> m [a]
  flattenM f = foldM step []
    where
      step acc x = do
        mx <- f x
        case mx of
          Just inner -> do
            inner' <- flattenM f inner
            pure $ acc ++ inner'
          Nothing -> pure $ acc ++ [x]

  isDefinitelyGreaterThan :: SimplifiedExpr -> SimplifiedExpr -> Bool
  isDefinitelyGreaterThan a b = case a .-. b of
    Right (Number' n)         -> n > 0
    Right (Fraction' num den) -> num > 0 && den > 0
    -- If simplification fails or not a clear number, assume not definitely greater
    _                         -> False

-- | Check if an expression is free of a variable,
-- meaning it does not contain the variable as a `Symbol` and is not dependent on it.
freeOf :: SimplifiedExpr -> SimplifiedExpr -> Bool
freeOf expr var
  | expr == var = False
  | isAtomic expr = True
  | otherwise = all (`freeOf` var) (operands expr)

-- | Check if an expression is free of all variables in a set.
setFreeOf :: Foldable t => SimplifiedExpr -> t SimplifiedExpr -> Bool
setFreeOf expr = all (freeOf expr)

-- | Extract the immediate operands of an expression.
operands :: Expr a -> [Expr a]
operands (Number' _)        = []
operands (Fraction' _ _)    = []
operands (Symbol' _)        = []
operands (Product' xs)      = NE.toList xs
operands (Sum' xs)          = NE.toList xs
operands (Quotient' x y)    = [x, y]
operands (Power' x y)       = [x, y]
operands (Function' _ args) = NE.toList args
operands (Factorial' x)     = [x]
operands (UnaryDiff' x)     = [x]
operands (BinaryDiff' x y)  = [x, y]

-- | Extract the symbols present in an expression.
symbols :: SimplifiedExpr -> HS.HashSet Text
symbols expr = case expr of
  Number' _        -> HS.empty
  Fraction' _ _    -> HS.empty
  Symbol' s        -> HS.singleton s
  Quotient' n d    -> HS.union (symbols n) (symbols d)
  UnaryDiff' x     -> symbols x
  BinaryDiff' x y  -> HS.union (symbols x) (symbols y)
  Product' factors -> HS.unions $ NE.toList $ NE.map symbols factors
  Sum' terms       -> HS.unions $ NE.toList $ NE.map symbols terms
  Power' b e       -> HS.union (symbols b) (symbols e)
  Factorial' expr' -> symbols expr'
  Function' _ args -> HS.unions $ NE.toList $ NE.map symbols args

-- | Extract the exponents of a variable in an expression.
exponents :: SimplifiedExpr -> Text -> HS.HashSet SimplifiedExpr
exponents (Number' _) _ = HS.empty
exponents (Fraction' _ _) _ = HS.empty
exponents (Symbol' s) x =
  if s == x then HS.singleton (mkNumber 1) else HS.empty
exponents (Power' b e) x =
  if b == mkSymbol x
    then HS.union (HS.singleton e) (exponents e x)
    else exponents e x
exponents (Product' factors) x =
  HS.unions $ NE.toList $ NE.map (`exponents` x) factors
exponents (Sum' terms) x =
  HS.unions $ NE.toList $ NE.map (`exponents` x) terms
exponents (Quotient' n d) x =
  HS.union (exponents n x) (exponents d x)
exponents (UnaryDiff' expr) x =
  exponents expr x
exponents (BinaryDiff' expr1 expr2) x =
  HS.union (exponents expr1 x) (exponents expr2 x)
exponents (Factorial' expr) x =
  exponents expr x
exponents (Function' _ args) x =
  HS.unions $ NE.toList $ NE.map (`exponents` x) args

-- | For a given expression and variable,
-- determine if the expression can be expressed in the form \(a \cdot x + b\)
-- where \(a\) and \(b\) are free of \(x\).
-- If so, return @Just (LinearForm a b)@, otherwise return @Nothing@.
linearForm :: SimplifiedExpr -> Text -> EvalResult (Maybe LinearForm)
linearForm expr (mkSymbol -> x)
  | expr == x =
      pure $ Just $ LinearForm (mkNumber 1) (mkNumber 1)
  | isAtomic expr =
      pure $ Just $ LinearForm (mkNumber 0) expr
  | isProduct expr = analyseProduct expr x
  | isSum expr = analyseSum expr x
  | freeOf expr x =
      pure $ Just $ LinearForm (mkNumber 0) expr
  | otherwise = pure Nothing
 where
  analyseProduct :: SimplifiedExpr -> SimplifiedExpr -> EvalResult (Maybe LinearForm)
  analyseProduct u v
    | freeOf u v = pure $ Just $ LinearForm (mkNumber 0) u
    | otherwise = do
        q <- u ./. v
        if freeOf q v
          then pure $ Just $ LinearForm q (mkNumber 0)
          else pure Nothing

  analyseSum :: SimplifiedExpr -> SimplifiedExpr -> EvalResult (Maybe LinearForm)
  analyseSum (Sum' tss) (Symbol' v) = do
    let headT = NE.head tss
    restT <- simplify $ mkSum $ NE.fromList (NE.tail tss)
    fstL <- linearForm headT v
    rstL <- linearForm restT v
    case (fstL, rstL) of
      (Just (LinearForm f1 f2), Just (LinearForm r1 r2)) -> do
        newCoeff <- f1 .+. r1
        newConst <- f2 .+. r2
        pure $ Just $ LinearForm newCoeff newConst
      _ -> pure Nothing
  analyseSum _ _ =
    throwError $
      UnsupportedOperation
        "linearForm: analyseSum called with non-sum expression"

-- | Substitute all occurrences of a pattern with a replacement in an expression.
--
-- Notice that this is a structural substitution,
-- meaning it will only replace an identical complete sub-expression.
-- >>> let expr = 2 * "x" + "x" :: UnsimplifiedExpr
-- >>> let pattern = Substitution.Pattern (mkSymbol "x")
-- >>> let replacement = Substitution.Replacement (mkSymbol "y")
-- >>> fmap toHaskell $ simplify expr >>= subs (pattern, replacement)
-- Right "3 * y"
subs ::
  (Substitution.Pattern SimplifiedExpr, Substitution.Replacement SimplifiedExpr) ->
  SimplifiedExpr ->
  EvalResult SimplifiedExpr
subs
  (unsimplify . Substitution.unPattern -> pat, unsimplify . Substitution.unReplacement -> repl)
  (unsimplify -> expr) =
    simplify $
      Substitution.subs
        ( Substitution.Pattern pat
        , Substitution.Replacement repl
        )
        expr

-- | Sequentially apply a list of substitutions to an expression,
-- where each substitution is applied to the result of the previous one.
--
-- This is useful when the substitutions may depend on each other or when order matters.
seqSubs ::
  [(Substitution.Pattern SimplifiedExpr, Substitution.Replacement SimplifiedExpr)] ->
  SimplifiedExpr ->
  EvalResult SimplifiedExpr
seqSubs [] expr = pure expr
seqSubs ((p, r) : rest) expr = do
  result <- subs (p, r) expr
  seqSubs rest result

-- | Apply substitutions concurrently to an expression.
--
-- The algorithm recursively traverses the expression tree, applying all substitutions at each node before moving to its children.
-- This means that if multiple substitutions match the same sub-expression, they will all be applied to
-- that sub-expression before any further traversal.
--
-- This is different from sequential substitution,
-- where substitutions are applied one after the other,
-- and the result of one substitution can affect the applicability of subsequent substitutions.
--
-- This is useful when the substitutions are independent and can be applied in any order, or when you want to ensure that all applicable substitutions are applied simultaneously.
concurSubs ::
  [(Substitution.Pattern SimplifiedExpr, Substitution.Replacement SimplifiedExpr)] ->
  SimplifiedExpr ->
  EvalResult SimplifiedExpr
concurSubs equations (unsimplify -> expr) = do
  let structuralEquations =
        [ ( Substitution.Pattern (unsimplify $ Substitution.unPattern p)
          , Substitution.Replacement (unsimplify $ Substitution.unReplacement r)
          )
        | (p, r) <- equations
        ]
  let result = Substitution.concurSubs structuralEquations expr
  simplify result

-- | Apply an effectful function to every immediate operand of an expression.
--  This keeps the traversal logic in one place for compound expressions.
mapOperands :: (SimplifiedExpr -> EvalResult SimplifiedExpr) -> SimplifiedExpr -> EvalResult SimplifiedExpr
mapOperands f = \case
  Sum' terms -> do
    terms' <- traverse f terms
    simplify $ mkSum terms'
  Product' factors -> do
    factors' <- traverse f factors
    simplify $ mkProduct factors'
  Quotient' n d -> do
    n' <- f n
    d' <- f d
    when (d' == mkNumber 0) $ throwError DivisionByZero
    simplify $ mkQuotient n' d'
  Power' b e -> (mkPower <$> f b <*> f e) >>= simplify
  Function' fname args -> mkFunction fname <$> traverse f args
  Factorial' x -> (f x >>= simplify . mkFactorial)
  UnaryDiff' x -> (f x >>= simplify . mkUnaryDiff)
  BinaryDiff' x y -> (mkBinaryDiff <$> f x <*> f y) >>= simplify
  atom -> pure atom

-- | Check if an expression is structurally zero (0 or 0/anything)
isZero :: Expr a -> Bool
isZero (Number' n)     = n == 0
isZero (Fraction' n _) = n == 0
isZero _               = False

-- | Build a normalized "rest" expression for a sum given the tail operands.
-- Returns \(0\) for an empty tail, the single element for a singleton tail,
-- or the simplified sum for multiple elements.
buildRestSum :: [SimplifiedExpr] -> EvalResult SimplifiedExpr
buildRestSum []  = pure $ mkNumber 0
buildRestSum [x] = pure x
buildRestSum xs  = simplify $ mkSum (NE.fromList xs)

-- | Build a normalized "rest" expression for a product given the tail operands.
-- Returns \(1\) for an empty tail, the single element for a singleton tail,
-- or the simplified product for multiple elements.
buildRestProduct :: [SimplifiedExpr] -> EvalResult SimplifiedExpr
buildRestProduct []  = pure $ mkNumber 1
buildRestProduct [x] = pure x
buildRestProduct xs  = simplify $ mkProduct (NE.fromList xs)
