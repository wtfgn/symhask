{-# LANGUAGE OverloadedLists #-}

module SymHask.Symbolic.Operators
    (
    ) where

import           SymHask.Symbolic                                        (Expression (..),
                                                                          ExpressionResult (..),
                                                                          Operands,
                                                                          isAtomic,
                                                                          toMaybe)
import           SymHask.Symbolic.Simplification.AutomaticSimplification (automaticSimplify)
import qualified Data.List.NonEmpty                                     as NE



-- ============================================================================
-- * Structure-Based Operators
-- ============================================================================

-- | Determines if an expression u is free of an expression t
-- (or does not contain t).
-- freeOf :: Expression -> Expression -> ExpressionResult Bool
-- freeOf u t
--   | u == t  = return False
--   | otherwise = do
--     simplified <- automaticSimplify u

--     case simplified of
--       -- atomic expressions
--       Number _ -> return True
--       Fraction _ _ -> return True
--       Symbol _ -> return True

--       -- compound expressions
--       Product xs -> allM (`freeOf` t) xs
--       Sum xs -> allM (`freeOf` t) xs
--       Quotient n d -> do
--         nFree <- freeOf n t
--         dFree <- freeOf d t
--         return (nFree && dFree)
--       Difference xs -> allM (`freeOf` t) xs
--       Power x y -> do
--         xFree <- freeOf x t
--         yFree <- freeOf y t
--         return (xFree && yFree)
--       Function _ args -> allM (`freeOf` t) args
--       Factorial x -> freeOf x t
--   where
--     allM :: (a -> ExpressionResult Bool) -> [a] -> ExpressionResult Bool
--     allM _ [] = return True
--     allM p (x : xs) = do
--       res <- p x
--       if res then allM p xs else return False
    -- This function checks if all elements in the list satisfy the predicate
    -- by recursively applying the predicate to each element.
    -- If any element does not satisfy the predicate, it returns False immediately.
    -- Otherwise, it returns True.
-- ============================================================================

completeSubExpressions :: Expression -> ExpressionResult [Expression]
completeSubExpressions u = do
  u' <- automaticSimplify u
  case u' of
    -- atomic expressions
    Number _ -> return [u']
    Fraction _ _ -> return [u']
    Symbol _ -> return [u']

    -- compound expressions
    Product xs  -> gatherSubExpressions u' xs

    Sum xs      -> gatherSubExpressions u' xs

    Quotient n d -> do
      nSub <- completeSubExpressions n
      dSub <- completeSubExpressions d
      return $ u' : nSub ++ dSub

    UnaryDifference x -> do
      xSub <- completeSubExpressions x
      return $ u' : xSub

    BinaryDifference x y -> do
      xSub <- completeSubExpressions x
      ySub <- completeSubExpressions y
      return $ u' : xSub ++ ySub

    Power x y     -> do
      xSub <- completeSubExpressions x
      ySub <- completeSubExpressions y
      return $ u' : xSub ++ ySub

    Factorial x     -> gatherSubExpressions u' [x]

    Function _ args -> gatherSubExpressions u' args
  where
    gatherSubExpressions :: Expression -> Operands -> ExpressionResult [Expression]
    gatherSubExpressions expr parts = do
      subExprsList <- mapM completeSubExpressions parts
      let subExprs = concat subExprsList
      return $ expr : subExprs

freeOf :: Expression -> Expression -> ExpressionResult Bool
freeOf u t = do
  subExprs <- completeSubExpressions u
  return $ t `notElem` subExprs

-- Checks if an algebraic expression u has the form ax+b,
-- where a and b are free of x.
-- Return (a, b) if the form matches, Nothing otherwise.
-- linearForm
--   :: Expression
--   -> Expression
--   -> ExpressionResult (Maybe (Expression, Expression))
-- linearForm u x = do
--   u' <- automaticSimplify u
--   if
--     | u' == x -> return $ Just (1, 0)
--     | isAtomic u' -> return $ Just (0, u')
--     | otherwise -> case u' of
--       Product _ =
--       -- Sum terms -> do
--       --   let f = linearForm (head terms) x
--       --   case f of
--       --     Nothing -> return Nothing
--       --     Just (a, b) -> return $ Just (a + 1, b)
