module SymHask.Symbolic.Operators
    ( freeOf
    ) where

import           SymHask.Symbolic                                        (Expression (..),
                                                                          ExpressionResult (..))
import           SymHask.Symbolic.Simplification.AutomaticSimplification (automaticSimplify)



-- ============================================================================
-- * Structure-Based Operators
-- ============================================================================

-- | Determines if an expression u is free of an expression t
-- (or does not contain t).
freeOf :: Expression -> Expression -> ExpressionResult Bool
freeOf u t
  | u == t  = return False
  | otherwise = do
    simplified <- automaticSimplify u

    case simplified of
      -- atomic expressions
      Number _ -> return True
      Fraction _ _ -> return True
      Symbol _ -> return True

      -- compound expressions
      Product xs -> allM (`freeOf` t) xs
      Sum xs -> allM (`freeOf` t) xs
      Quotient n d -> do
        nFree <- freeOf n t
        dFree <- freeOf d t
        return (nFree && dFree)
      Difference xs -> allM (`freeOf` t) xs
      Power x y -> do
        xFree <- freeOf x t
        yFree <- freeOf y t
        return (xFree && yFree)
      Function _ args -> allM (`freeOf` t) args
      Factorial x -> freeOf x t
  where
    allM :: (a -> ExpressionResult Bool) -> [a] -> ExpressionResult Bool
    allM _ [] = return True
    allM p (x : xs) = do
      res <- p x
      if res then allM p xs else return False
    -- This function checks if all elements in the list satisfy the predicate
    -- by recursively applying the predicate to each element.
    -- If any element does not satisfy the predicate, it returns False immediately.
    -- Otherwise, it returns True.
-- ============================================================================




