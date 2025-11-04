{-# LANGUAGE MultiWayIf #-}

module SymHask.Symbolic.Basic
    ( allFreeOf
    , containParameters
    , freeOf
    , isNumerical
    , symbols
    , treeSize
    , separateFactors
    , completeSubExprs
    , evenOdd
    ) where

import           Control.Monad
import qualified Data.HashSet                       as HS
import qualified Data.List.NonEmpty                 as NE
import           Data.Text                          (Text)
import           SymHask.Symbolic
import           SymHask.Symbolic.Basic.Substitution
import           SymHask.Symbolic.Simplification

data FunctionParity
  = EvenFunc
  | OddFunc
  | NeitherFunc
  deriving (Eq, Show)

freeOf :: SimplifiedExpr -> SimplifiedExpr -> Bool
freeOf expr var
  | expr == var = False
  | isAtomic expr = True
  | otherwise = all (`freeOf` var) (operands expr)

allFreeOf :: (Foldable f) => SimplifiedExpr -> f SimplifiedExpr -> Bool
allFreeOf var = all (`freeOf` var)

operands :: Expr s -> [Expr s]
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

containParameters :: SimplifiedExpr -> Text -> Bool
containParameters simplified param =
  HS.member param (symbols simplified)

isNumerical :: SimplifiedExpr -> Bool
isNumerical = \case
  Number' _     -> True
  Fraction' _ _ -> True
  Pi'         -> True
  E'         -> True
  Symbol' _     -> False
  Quotient' n d  -> isNumerical n && isNumerical d
  UnaryDiff' x   -> isNumerical x
  BinaryDiff' x y -> isNumerical x && isNumerical y
  Product' factors    -> all isNumerical factors
  Sum' terms        -> all isNumerical terms
  Power' b e -> isNumerical b && isNumerical e
  Factorial' expr  -> isNumerical expr
  Function' _ args -> all isNumerical args

treeSize :: SimplifiedExpr -> Int
treeSize = \case
  Number' _     -> 1
  Fraction' _ _ -> 3
  Symbol' _     -> 1
  Quotient' n d  -> 1 + treeSize n + treeSize d
  UnaryDiff' x   -> 1 + treeSize x
  BinaryDiff' x y -> 1 + treeSize x + treeSize y
  Product' factors    -> 1 + sum (NE.map treeSize factors)
  Sum' terms        -> 1 + sum (NE.map treeSize terms)
  Power' b e -> 1 + treeSize b + treeSize e
  Factorial' expr  -> 1 + treeSize expr
  Function' _ args -> 1 + sum (NE.map treeSize args)

completeSubExprs :: SimplifiedExpr -> HS.HashSet SimplifiedExpr
completeSubExprs expr
  | null (operands expr) = HS.singleton expr
  | otherwise     = HS.insert expr (HS.unions subSets)
  where
    subSets  = map completeSubExprs $ operands expr

-- | Separate factors into parts free of variable x and parts dependent on x
-- For expression u*v*w..., separates into (free_part, dependent_part) where:
-- - free_part contains factors that don't depend on x
-- - dependent_part contains factors that do depend on x
separateFactors :: SimplifiedExpr -> SimplifiedExpr -> EvalResult (SimplifiedExpr, SimplifiedExpr)
separateFactors (Product' factors) var =
  foldM processFactor (mkNumber 1, mkNumber 1) (NE.toList factors)
  where
    -- Process a single factor
    processFactor
      :: (SimplifiedExpr, SimplifiedExpr)
      -> SimplifiedExpr
      -> EvalResult (SimplifiedExpr, SimplifiedExpr)
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

evenOdd :: SimplifiedExpr -> Text -> EvalResult FunctionParity
evenOdd expr x = do
  negX <- simplify (negate (mkSymbol x) :: UnsimplifiedExpr)
  substituted <- subs
    (Pattern (mkSymbol x), Replacement negX)
    expr
  if
    | expr .-. substituted == pure (mkNumber 0) -> return EvenFunc
    | expr .+. substituted == pure (mkNumber 0) -> return OddFunc
    | otherwise                                 -> return NeitherFunc
