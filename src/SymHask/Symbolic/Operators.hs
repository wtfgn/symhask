{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE OverloadedLists #-}

module SymHask.Symbolic.Operators
    ( completeSubExpressions
    , freeOf
    , linearForm
    ) where

import           Control.Monad.Error.Class                               (throwError)
import qualified Data.List.NonEmpty                                      as NE
import           Data.Text                                               (Text)
import           SymHask.Symbolic                                        (Expression (..),
                                                                          ExpressionError (..),
                                                                          ExpressionResult,
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
  Right u' -> if
    | u' == t     -> False
    | isAtomic u' -> True
    | otherwise   -> all (`freeOf` t) (getOperands u')
  Left _ -> False

-- ============================================================================
-- * Linear Forms
-- ============================================================================

type LinearForm = (Expression, Expression) -- (a, b) in ax + b

linearForm :: Expression -> Text -> ExpressionResult (Maybe LinearForm)
linearForm u x = do
  u' <- automaticSimplify u
  k <- analyzeLinearForm u' x
  case k of
    Just (a, b) -> do
      a' <- automaticSimplify a
      b' <- automaticSimplify b
      return $ Just (a', b')
    Nothing -> return Nothing

analyzeLinearForm :: Expression -> Text -> ExpressionResult (Maybe LinearForm)
analyzeLinearForm u' x
  | u' == Symbol x = return $ Just (1, 0)
  | isAtomic u' = return $ Just (0, u')
  | isProduct u' = analyzeProductForm u' x
  | isSum u' = analyzeSumForm u' x
  | freeOf u' (Symbol x) = return $ Just (0, u')
  | otherwise = return Nothing

analyzeProductForm :: Expression -> Text -> ExpressionResult (Maybe LinearForm)
analyzeProductForm u'@(Product _) x
  | freeOf u' (Symbol x) = return $ Just (0, u')
  | freeOf (u' / Symbol x) (Symbol x) = return $ Just (u' / Symbol x, 0)
  | otherwise = return Nothing
analyzeProductForm u _ = throwError $
  UnsupportedOperation "analyzeProductForm: not a product expression" u

analyzeSumForm :: Expression -> Text -> ExpressionResult (Maybe LinearForm)
analyzeSumForm u'@(Sum ts) x = do
  let
    firstTerm = NE.head ts
    restExpr = u' - firstTerm
  firstLinear <- linearForm firstTerm x
  restLinear <- linearForm restExpr x
  combineLinearForms firstLinear restLinear
analyzeSumForm u _ = throwError $
  UnsupportedOperation "analyzeSumForm: not a sum expression" u

combineLinearForms
  :: Maybe LinearForm -> Maybe LinearForm
  -> ExpressionResult (Maybe LinearForm)
combineLinearForms (Just (a1, b1)) (Just (a2, b2)) = do
  return $ Just (a1 + a2, b1 + b2)
combineLinearForms _ _ = return Nothing
