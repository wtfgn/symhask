module SymHask.Symbolic.Basic.Utils
    ( binomial
    , buildRestProduct
    , buildRestSum
    , eitherToMaybe
    , eliminateBy
    , flattenM
    , isDefinitelyGreaterThan
    ) where

import           Control.Monad                   (foldM)
import qualified Data.List.NonEmpty              as NE
import           SymHask.Symbolic
import           SymHask.Symbolic.Simplification

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

eitherToMaybe :: Either e a -> Maybe a
eitherToMaybe = either (const Nothing) Just

{- | Build a normalized "rest" expression for a sum given the tail operands.
Returns 0 for an empty tail, the single element for a singleton tail,
or the simplified sum for multiple elements.
-}
buildRestSum :: [SimplifiedExpr] -> EvalResult SimplifiedExpr
buildRestSum []  = pure $ mkNumber 0
buildRestSum [x] = pure x
buildRestSum xs  = simplify $ mkSum (NE.fromList xs)

{- | Build a normalized "rest" expression for a product given the tail operands.
Returns 1 for an empty tail, the single element for a singleton tail,
or the simplified product for multiple elements.
-}
buildRestProduct :: [SimplifiedExpr] -> EvalResult SimplifiedExpr
buildRestProduct []  = pure $ mkNumber 1
buildRestProduct [x] = pure x
buildRestProduct xs  = simplify $ mkProduct (NE.fromList xs)

-- integer binomial
binomial :: Integer -> Integer -> Integer
binomial n k
  | k < 0 || k > n = 0
  | otherwise = product [n - k + 1 .. n] `div` product [1 .. k]
