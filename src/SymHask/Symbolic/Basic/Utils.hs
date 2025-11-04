module SymHask.Symbolic.Basic.Utils
  ( eliminateBy
  , flattenM
  , isDefinitelyGreaterThan
  ) where

import Control.Monad (foldM)
import SymHask.Symbolic
import SymHask.Symbolic.Simplification

-- | Generic elimination: keep elements that are not dominated by any other.
--   `d x y` should be True when x dominates y (i.e. x > y).
--   Order of survivors is preserved.
eliminateBy :: (a -> a -> Bool) -> [a] -> [a]
eliminateBy _ []  = []
eliminateBy _ [x] = [x]
eliminateBy d (x:xs)
  | any (`d` x) xs = eliminateBy d xs
  | otherwise      = x : eliminateBy d (filter (not . d x) xs)

-- | Monadic flattener.
--   Given a function that optionally returns a list of inner elements to splice,
--   recursively flattens those inner lists.
--
--   Example usage:
--     flattenM (\case Max' inner -> pure $ Just (HS.toList inner); _ -> pure Nothing) xs
flattenM :: Monad m => (a -> m (Maybe [a])) -> [a] -> m [a]
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