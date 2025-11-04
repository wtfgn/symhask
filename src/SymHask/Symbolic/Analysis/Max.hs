{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}

module SymHask.Symbolic.Analysis.Max
    ( maxExpr
    , maxExponent
    ) where

import           Control.Monad.Error.Class
import qualified Data.List.NonEmpty                              as NE
import           Data.Text                                       (Text)
import           SymHask.Symbolic
import           SymHask.Symbolic.Simplification
import qualified Data.HashSet                                    as HS
import Control.Monad (foldM)

pattern Max' :: HS.HashSet SimplifiedExpr -> SimplifiedExpr
pattern Max' exprSet <- Function' "max" (NE.toList -> (HS.fromList -> exprSet))

mkMax :: HS.HashSet SimplifiedExpr -> SimplifiedExpr
mkMax exprSet = mkFunction "max" (NE.fromList (HS.toList exprSet))

maxExpr :: HS.HashSet SimplifiedExpr -> EvalResult SimplifiedExpr
maxExpr exprSet = case HS.toList exprSet of
  [] -> throwError $ UnsupportedOperation "maxExpr: empty set"
  [Max' xs] -> maxExpr xs  -- Flatten nested max
  [x] -> return x
  xs -> do
    flattened <- flattenMax xs
     -- Now eliminate comparable expressions
     -- First, simplify all expressions
    let survivors = eliminateComparable flattened
    case survivors of
      []  -> throwError $
        UnsupportedOperation "maxExpr: no survivors after elimination"
      [x] -> return x
      _   -> return $ mkMax (HS.fromList survivors)

-- Eliminate expressions that are definitely less than others
eliminateComparable :: [SimplifiedExpr] -> [SimplifiedExpr]
eliminateComparable [] = []
eliminateComparable [x] = [x]
eliminateComparable (x:xs) =
  if any (`isDefinitelyGreaterThan` x) xs  -- Check if anything in xs dominates x
  then eliminateComparable xs            -- x is eliminated, continue without it
  else x : eliminateComparable (filter (not . isDefinitelyGreaterThan x) xs)
      -- x survives, eliminate anything x dominates, continue recursively

-- -- Flatten nested Max expressions into a single list
-- -- Max({3, Max({2, x})}) becomes [3, 2, x]
flattenMax :: [SimplifiedExpr] -> EvalResult [SimplifiedExpr]
flattenMax = foldM flattenSingle []
  where
    flattenSingle :: [SimplifiedExpr] -> SimplifiedExpr -> EvalResult [SimplifiedExpr]
    flattenSingle acc (Max' innerExprs) = do
      -- Recursively flatten the inner Max expressions
      innerFlattened <- flattenMax (HS.toList innerExprs)
      return $ acc ++ innerFlattened
    flattenSingle acc expr = return $ acc ++ [expr]


isDefinitelyGreaterThan :: SimplifiedExpr -> SimplifiedExpr -> Bool
isDefinitelyGreaterThan a b = case a .-. b of
  Right (Number' n)         -> n > 0
  Right (Fraction' num den) -> num > 0 && den > 0
  -- If simplification fails or not a clear number,
  -- assume not definitely greater
  _                           -> False

maxExponent :: SimplifiedExpr -> Text -> EvalResult SimplifiedExpr
maxExponent expr x = maxExpr $ collectExponents expr x

collectExponents :: SimplifiedExpr -> Text -> HS.HashSet SimplifiedExpr
collectExponents (Number' _) _ = HS.empty
collectExponents (Fraction' _ _) _ = HS.empty
collectExponents (Symbol' s) x =
  if s == x then HS.singleton (mkNumber 1) else HS.empty
collectExponents (Power' b e) x =
  if b == mkSymbol x
    then HS.union (HS.singleton e) (collectExponents e x)
    else collectExponents e x
collectExponents (Product' factors) x =
  HS.unions $ NE.toList $ NE.map (`collectExponents` x) factors
collectExponents (Sum' terms) x =
  HS.unions $ NE.toList $ NE.map (`collectExponents` x) terms
collectExponents (Quotient' n d) x =
  HS.union (collectExponents n x) (collectExponents d x)
collectExponents (UnaryDiff' expr) x =
  collectExponents expr x
collectExponents (BinaryDiff' expr1 expr2) x =
  HS.union (collectExponents expr1 x) (collectExponents expr2 x)
collectExponents (Factorial' expr) x =
  collectExponents expr x
collectExponents (Function' _ args) x =
  HS.unions $ NE.toList $ NE.map (`collectExponents` x) args