{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE OverloadedLists #-}

module SymHask.Symbolic.Operators
    (
    ) where

import qualified Data.List.NonEmpty                                      as NE
import           SymHask.Symbolic                                        (Expression (..),
                                                                          ExpressionResult (..),
                                                                          Operands,
                                                                          getOperands,
                                                                          isAtomic,
                                                                          isProduct,
                                                                          isSum)
import           SymHask.Symbolic.Simplification.AutomaticSimplification (automaticSimplify)



-- ============================================================================
-- * Structure-Based Operators
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

freeOf :: Expression -> Expression -> Bool
freeOf u t = case automaticSimplify u of
  ExpressionSuccess u' -> if
    | u' == t     -> False
    | isAtomic u' -> True
    | otherwise   -> all (`freeOf` t) (getOperands u')
  _ -> False

-- ============================================================================
-- * Linear Forms
-- ============================================================================

type LinearForm = (Expression, Expression) -- (a, b) in ax + b

linearForm :: Expression -> Expression -> ExpressionResult (Maybe LinearForm)
linearForm u x = do
  u' <- automaticSimplify u
  analyzeLinearForm u' x


analyzeLinearForm :: Expression -> Expression -> ExpressionResult (Maybe LinearForm)
analyzeLinearForm u' x
  | u' == x = return $ Just (1, 0)
  | isAtomic u' = return $ Just (0, u')
  | isProduct u' = analyzeProductForm u' x
  | isSum u' = analyzeSumForm u' x
  | freeOf u' x = return $ Just (0, u')
  | otherwise = return Nothing

analyzeProductForm :: Expression -> Expression -> ExpressionResult (Maybe LinearForm)
analyzeProductForm u' x
  | freeOf u' x = return $ Just (0, u')
  | freeOf (u' / x) x = return $ Just (u' / x, 0)
  | otherwise = return Nothing

analyzeSumForm :: Expression -> Expression -> ExpressionResult (Maybe LinearForm)
analyzeSumForm u'@(Sum ts) x = do
  let
    firstTerm = NE.head ts
    restExpr = u' - firstTerm

  firstLinear <- linearForm firstTerm x
  restLinear <- linearForm restExpr x
  combineLinearForms firstLinear restLinear
analyzeSumForm _ _ = ExpressionError "analyzeSumForm: not a sum"

combineLinearForms
  :: Maybe LinearForm -> Maybe LinearForm
  -> ExpressionResult (Maybe LinearForm)
combineLinearForms (Just (a1, b1)) (Just (a2, b2)) = do
  a <- automaticSimplify (a1 + a2)
  b <- automaticSimplify (b1 + b2)
  return $ Just (a, b)
combineLinearForms _ _ = return Nothing
