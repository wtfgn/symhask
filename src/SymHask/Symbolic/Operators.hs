{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PatternSynonyms #-}

module SymHask.Symbolic.Operators
    ( allFreeOf
    , completeSubExpressions
    , containParameters
    , freeOf
    , getAllSymbols
    , isNumerical
    , linearForm
    , substitute
    , treeSize
    , trigFreeOf
    , sequentialSubstitute
    ) where

import           Control.Monad.Error.Class                               (throwError)
import qualified Data.List.NonEmpty                                      as NE
import qualified Data.Set                                                as Set

import           Data.Text                                               (Text)
import           SymHask.Symbolic                                        (Expression (..),
                                                                          ExpressionError (..),
                                                                          ExpressionResult,
                                                                          Operands,
                                                                          getOperands,
                                                                          isAtomic,
                                                                          isProduct,
                                                                          isSum,
                                                                          pattern Cos',
                                                                          pattern Cot',
                                                                          pattern Csc',
                                                                          pattern E',
                                                                          pattern Pi',
                                                                          pattern Sec',
                                                                          pattern Sin',
                                                                          pattern Tan')
import           SymHask.Symbolic.Simplification.AutomaticSimplification (automaticSimplify)
import Control.Monad (foldM)

-- ============================================================================
-- * Structure-Based Operators
-- ============================================================================
completeSubExpressions :: Expression -> ExpressionResult (Set.Set Expression)
completeSubExpressions u = do
  u' <- automaticSimplify u
  case u' of
    -- atomic expressions
    Number _ -> return $ Set.singleton u'
    Fraction _ _ -> return $ Set.singleton u'
    Symbol _ -> return $ Set.singleton u'

    -- compound expressions
    Product xs  -> gatherSubExpressions u' xs
    Sum xs      -> gatherSubExpressions u' xs

    Quotient n d -> do
      nSub <- completeSubExpressions n
      dSub <- completeSubExpressions d
      return $ Set.insert u' (Set.union nSub dSub)

    UnaryDifference x -> do
      xSub <- completeSubExpressions x
      return $ Set.insert u' xSub

    BinaryDifference x y -> do
      xSub <- completeSubExpressions x
      ySub <- completeSubExpressions y
      return $ Set.insert u' (Set.union xSub ySub)

    Power x y     -> do
      xSub <- completeSubExpressions x
      ySub <- completeSubExpressions y
      return $ Set.insert u' (Set.union xSub ySub)

    Factorial x     -> gatherSubExpressions u' [x]
    Function _ args -> gatherSubExpressions u' args
  where
    gatherSubExpressions :: Expression -> Operands -> ExpressionResult (Set.Set Expression)
    gatherSubExpressions expr parts = do
      subExprsList <- mapM completeSubExpressions parts
      let subExprs = Set.unions subExprsList
      return $ Set.insert expr subExprs

freeOf :: Expression -> Expression -> Bool
freeOf u t =
  case (automaticSimplify u, automaticSimplify t) of
    (Right u', Right t') -> if
      | u' == t'    -> False
      | isAtomic u' -> True
      | otherwise   -> all (`freeOf` t') (getOperands u')
    _ -> False  -- If simplification fails, assume not free

-- determines if u is free of all expressions in a set (or list) S
-- u and elements in s will be simplified in freeOf
allFreeOf :: (Foldable f) => Expression -> f Expression -> Bool
allFreeOf u = all (`freeOf` u)

-- returns true if an algebraic expression u
-- is free of trigonometric functions (sin, cos, tan, cot, sec, csc)
-- and false otherwise.
trigFreeOf :: Expression -> Bool
trigFreeOf u =
  case automaticSimplify u of
    Right u' -> if
      | isTrigFunction u' -> False
      | isAtomic u'       -> True
      | otherwise         -> all trigFreeOf (getOperands u')
    Left _ -> False  -- If simplification fails, assume not free
  where
    isTrigFunction :: Expression -> Bool
    isTrigFunction = \case
      Sin' _ -> True
      Cos' _ -> True
      Tan' _ -> True
      Cot' _ -> True
      Sec' _ -> True
      Csc' _ -> True
      _      -> False

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

-- Assume u is already simplified
analyzeLinearForm :: Expression -> Text -> ExpressionResult (Maybe LinearForm)
analyzeLinearForm u' x
  | u' == Symbol x = return $ Just (1, 0)
  | isAtomic u' = return $ Just (0, u')
  | isProduct u' = analyzeProductForm u' x
  | isSum u' = analyzeSumForm u' x
  | freeOf u' (Symbol x) = return $ Just (0, u')
  | otherwise = return Nothing

-- Assume u is already simplified
analyzeProductForm :: Expression -> Text -> ExpressionResult (Maybe LinearForm)
analyzeProductForm u'@(Product _) x
  | freeOf u' (Symbol x) = return $ Just (0, u')
  | freeOf (u' / Symbol x) (Symbol x) = return $ Just (u' / Symbol x, 0)
  | otherwise = return Nothing
analyzeProductForm u _ = throwError $
  UnsupportedOperation "analyzeProductForm: not a product expression" u

-- Assume u is already simplified
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

-- ============================================================================
-- Symbols
-- ============================================================================

-- Returns a set of symbols in u
getAllSymbols :: Expression -> ExpressionResult (Set.Set Text)
getAllSymbols u = do
  u' <- automaticSimplify u
  case u' of
    Number _ -> return Set.empty
    Fraction _ _ -> return Set.empty
    Symbol s -> return $ Set.singleton s

    Product xs -> gatherSymbols xs
    Sum xs -> gatherSymbols xs

    Quotient n d -> do
      nSym <- getAllSymbols n
      dSym <- getAllSymbols d
      return $ Set.union nSym dSym

    UnaryDifference x -> getAllSymbols x
    BinaryDifference x y -> do
      xSym <- getAllSymbols x
      ySym <- getAllSymbols y
      return $ Set.union xSym ySym

    Power x y -> do
      xSym <- getAllSymbols x
      ySym <- getAllSymbols y
      return $ Set.union xSym ySym

    Factorial x -> getAllSymbols x
    Function _ args -> gatherSymbols args
  where
    gatherSymbols :: Operands -> ExpressionResult (Set.Set Text)
    gatherSymbols parts = do
      symList <- mapM getAllSymbols parts
      return $ Set.unions symList

-- ============================================================================
-- * Contain_parameters
-- ============================================================================

-- returns true if the algebraic expression u contains any symbols other
-- than the symbol x and false otherwise.
containParameters :: Expression -> Text -> Bool
containParameters u x =
  case getAllSymbols u of
    Right symbolSet ->
      not (Set.null symbolSet) && symbolSet /= Set.singleton x
    Left _ -> False  -- If symbols extraction fails, assume no parameters

  -- ============================================================================
-- * isNumerical
-- ============================================================================

isNumerical :: Expression -> Bool
isNumerical u =
  case automaticSimplify u of
    Right u' -> case u' of
      -- Integer or Fraction
      Number _             -> True
      Fraction _ _         -> True

      -- Symbols pi or e
      Pi'                  -> True
      E'                   -> True

      -- Compound expressions with numerical operands
      Product xs           -> all isNumerical xs
      Sum xs               -> all isNumerical xs
      Quotient n d         -> isNumerical n && isNumerical d
      UnaryDifference x    -> isNumerical x
      BinaryDifference x y -> isNumerical x && isNumerical y
      Power x y            -> isNumerical x && isNumerical y
      Factorial x          -> isNumerical x
      Function _ args      -> all isNumerical args

      _                    -> False

    Left _ -> False  -- If simplification fails, assume not numerical

-- ============================================================================
-- * Tree Size
-- ============================================================================

-- | Calculate the tree-size of an expression
-- Tree-size is the number of symbols, integers, algebraic operators, and function names
-- For example: (x + sin(x) + 2) * x^3 has tree-size 9
-- Components: x, +, sin, x, 2, *, x, ^, 3
treeSize :: Expression -> Int
treeSize u =
  case automaticSimplify u of
    Right u' -> treeSize' u'
    Left _   -> 0  -- If simplification fails, assume tree size is 0
  where
    treeSize' :: Expression -> Int
    treeSize' = \case
      -- Atomic expressions count as 1
      Number _     -> 1  -- The integer itself
      Fraction _ _ -> 3   -- numerator + fraction operator + denominator
      Symbol _     -> 1  -- The symbol itself

      -- Compound expressions: operator + operands
      Product xs           -> 1 + sum (NE.map treeSize xs)  -- * operator + operands
      Sum xs               -> 1 + sum (NE.map treeSize xs)  -- + operators + operands
      Quotient n d         -> 1 + treeSize n + treeSize d  -- / operator + operands
      UnaryDifference x    -> 1 + treeSize x  -- - operator + operand
      BinaryDifference x y -> 1 + treeSize x + treeSize y  -- - operator + operands
      Power x y            -> 1 + treeSize x + treeSize y  -- ^ operator + operands
      Factorial x          -> 1 + treeSize x  -- ! operator + operand
      Function _ args   -> 1 + sum (NE.map treeSize args)  -- function name + arguments

-- ============================================================================
-- Substitute
-- ============================================================================

-- | Apply a transformation function to all sub-expressions in an expression
-- substitute u f applies function f to every sub-expression of u, including u itself
--
-- IMPORTANT: The transformation function f MUST handle all possible Expression cases
-- or include a catch-all pattern (_ -> Nothing) to avoid runtime errors.
--
-- Example of SAFE usage:
-- @
-- let safeMapping = \case
--       Symbol "x" -> Just (Number 5)
--       Symbol "y" -> Just (Symbol "z")
--       _ -> Nothing  -- ← REQUIRED catch-all pattern
-- @
--
-- Note that it is a structural substitution (based on the expression tree structure)
-- @substitute ("a" + "b" + "c") (\case "a" :+: "b" -> return "x"; _ -> Nothing)
-- = "a" + "b" + "c"@
-- This is because a + b is not a complete sub-expression
-- However,
-- @substitute ("a" + "b" + "c") (\case (Symbol "a") -> return "x" - "b"; _ -> Nothing)
-- = "c" + "x"@
--
-- For concurrent substitutions (multiple transformations applied at once),
-- You can add more patterns to the same function f.
-- For sequential substitutions (one transformation after another),
-- use the 'sequentialSubstitute' function.
substitute :: Expression -> (Expression -> Maybe Expression) -> ExpressionResult Expression
substitute u f =
  case automaticSimplify u of
    Right u' -> substitute' u' >>= automaticSimplify
    Left err -> Left err
  where
    substitute' :: Expression -> ExpressionResult Expression
    substitute' expr = do
      -- First check if we should transform this expression directly
      case f expr of
        Just result -> return result
        Nothing -> case expr of
          -- If no direct transformation, recurse into sub-expressions
          -- Atomic expressions - no sub-expressions to process
          Number _ -> return expr
          Fraction _ _ -> return expr
          Symbol _ -> return expr

          -- Compound expressions - recurse into operands
          Product xs -> Product <$> mapM (`substitute` f) xs
          Sum xs -> Sum <$> mapM (`substitute` f) xs
          Quotient n d -> Quotient <$> substitute n f <*> substitute d f
          UnaryDifference x -> UnaryDifference <$> substitute x f
          BinaryDifference x y -> BinaryDifference <$> substitute x f <*> substitute y f
          Power x y -> Power <$> substitute x f <*> substitute y f
          Factorial x -> Factorial <$> substitute x f
          Function fname args -> Function fname <$> mapM (`substitute` f) args

-- Apply a list of transformation functions in sequence to all sub-expressions
-- Let L = [f1, f2, ..., fn] be a list of transformation functions
-- @sequentialSubstitute u L@ is defined as
-- @sequentialSubstitute u L = substitute (...(substitute (substitute u f1) f2)...) fn@
sequentialSubstitute
  :: Expression
  -> [Expression -> Maybe Expression]
  -> ExpressionResult Expression
sequentialSubstitute = foldM substitute

