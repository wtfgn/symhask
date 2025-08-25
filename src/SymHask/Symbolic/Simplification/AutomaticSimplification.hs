{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE OverloadedLists #-}

module SymHask.Symbolic.Simplification.AutomaticSimplification
    ( automaticSimplify
    ) where

import qualified Data.List.NonEmpty                             as NE
import           SymHask.Symbolic                               (Expression (..),
                                                                 ExpressionResult (..),
                                                                 getConst,
                                                                 getPowerBase,
                                                                 getPowerExponent,
                                                                 getTerm,
                                                                 isConstant)
import           SymHask.Symbolic.Simplification.RationalNumber (simplifyRNE,
                                                                 simplifyRationalNumber)
import           SymHask.Symbolic.Factorial                     (factorial)

-- This module is intended to handle automatic simplification of symbolic expressions.
-- ============================================================================

-- ============================================================================
-- * Main Simplification Function
-- ============================================================================
automaticSimplify :: Expression -> ExpressionResult Expression
automaticSimplify = \case
  -- Integers and Symbols are already simplified
  u@(Number _) -> return u
  u@(Symbol _) -> return u

  -- Fractions are simplified using the rational simplification function
  u@(Fraction _ _) -> simplifyRationalNumber u

  -- Compound expressions are simplified by recursively simplifying their operands
  Power b e -> do
    b' <- automaticSimplify b
    e' <- automaticSimplify e
    simplifyPower $ Power b' e'

  Product xs -> do
    xs' <- traverse automaticSimplify xs
    simplifyProduct $ Product xs'

  Sum xs -> do
    xs' <- traverse automaticSimplify xs
    simplifySum $ Sum xs'

  Quotient u v -> do
    u' <- automaticSimplify u
    v' <- automaticSimplify v
    simplifyQuotient $ Quotient u' v'

  UnaryDifference u -> do
    u' <- automaticSimplify u
    simplifyDifference $ UnaryDifference u'

  BinaryDifference u v -> do
    u' <- automaticSimplify u
    v' <- automaticSimplify v
    simplifyDifference $ BinaryDifference u' v'

  Factorial u -> do
    u' <- automaticSimplify u
    simplifyFactorial $ Factorial u'

  Function name args -> do
    args' <- traverse automaticSimplify args
    simplifyFunction $ Function name args'

-- ============================================================================
-- * Simplification of Powers
-- ============================================================================
simplifyPower :: Expression -> ExpressionResult Expression
simplifyPower = \case
  -- 0^w = 0, w is a positive integer or fraction
  Power (Number 0) (Number y)
    | y > 0 -> return $ Number 0
    | otherwise -> ExpressionUndefined "0 raised to a non-positive power is undefined"
  Power (Number 0) (Fraction n d)
    | n > 0 && d > 0 -> return $ Number 0
    | otherwise -> ExpressionUndefined "0 raised to a non-positive power is undefined"

  -- 1^w = 1 for any w
  Power (Number 1) _ -> return $ Number 1

  -- v^w = simplifyIntegerPower v w, where w is an integer
  Power v (Number w) -> simplifyIntegerPower v w

  -- If no rules apply, return the expression unchanged
  u -> return u

simplifyIntegerPower :: Expression -> Integer -> ExpressionResult Expression
simplifyIntegerPower v@(Number _) n = simplifyRNE $ Power v (Number n)
simplifyIntegerPower v@(Fraction _ _) n = simplifyRNE $ Power v (Number n)
simplifyIntegerPower _ 0 = return $ Number 1
simplifyIntegerPower v 1 = return v
simplifyIntegerPower (Power r s) n =
  case simplifyProduct (Product [s, Number n]) of
    ExpressionSuccess (Number p) -> simplifyIntegerPower r p
    ExpressionSuccess p          -> return $ Power r p
    ExpressionError err          -> ExpressionError err
    ExpressionUndefined msg      -> ExpressionUndefined msg
simplifyIntegerPower (Product xs) n =
  case traverse (`simplifyIntegerPower` n) xs of
    ExpressionSuccess exprs -> simplifyProduct $ Product exprs
    ExpressionError err     -> ExpressionError err
    ExpressionUndefined msg -> ExpressionUndefined msg
simplifyIntegerPower v n = return $ Power v (Number n)

-- ============================================================================
-- * Simplification of Products
-- ============================================================================
simplifyProduct :: Expression -> ExpressionResult Expression
simplifyProduct = \case
  Product [x] -> return x
  Product xs
    | any isZero xs -> return $ Number 0
    | otherwise -> do
      v <- simplifyProductStep $ NE.toList xs
      case v of
        []  -> return $ Number 1
        [u] -> return u
        _   -> return $ Product $ NE.fromList v
  _ -> ExpressionError "Expected a Product expression"
  where
    isZero (Number 0) = True
    isZero _          = False

-- length L < 2 does not apply
simplifyProductStep :: [Expression] -> ExpressionResult [Expression]
simplifyProductStep [] = return []
simplifyProductStep [u] = return [u]

-- Suppose L = [u1, u2] and at least one operand is a product
simplifyProductStep [Product ps, Product qs] =
  mergeProducts (NE.toList ps) (NE.toList qs)
simplifyProductStep [Product ps, u2] =
  mergeProducts (NE.toList ps) [u2]
simplifyProductStep [u1, Product qs] =
  mergeProducts [u1] (NE.toList qs)

-- Suppose L = [u1, u2] and neither operand is a product
simplifyProductStep [Number 1, u2] = return [u2]
simplifyProductStep [u1, Number 1] = return [u1]
simplifyProductStep [u1, u2]
  | isConstant u1 && isConstant u2 = do
    p <- simplifyRNE $ Product [u1, u2]
    case p of
      Number 1 -> return []
      _        -> return [p]
  | getPowerBase u1 == getPowerBase u2 = do
    b1 <- getPowerBase u1
    e1 <- getPowerExponent u1
    e2 <- getPowerExponent u2
    s <- simplifySum $ Sum [e1, e2]
    p <- simplifyPower $ Power b1 s
    if p == Number 1
      then return []
      else return [p]
  | u2 < u1 = return [u2, u1]
  | otherwise = return [u1, u2]

-- Suppose L = [u1, u2, ..., uN] with N > 2
simplifyProductStep (x : xs) = do
  w <- simplifyProductStep xs
  case x of
    Product ps -> mergeProducts (NE.toList ps) w
    _          -> mergeProducts [x] w

mergeProducts :: [Expression] -> [Expression] -> ExpressionResult [Expression]
mergeProducts pss [] = return pss
mergeProducts [] qss = return qss
mergeProducts pss@(p : ps) qss@(q : qs) = do
  h <- simplifyProductStep [p, q]
  case h of
    [] -> mergeProducts ps qs
    [u] -> do
      rest <- mergeProducts ps qs
      return (u : rest)
    [u1, u2] -> if
      | u1 == p && u2 == q -> do
        rest <- mergeProducts ps qss
        return (p : rest)
      | u1 == q && u2 == p -> do
        rest <- mergeProducts pss qs
        return (q : rest)
      | otherwise -> ExpressionError "Unexpected result from mergeProducts"
    _ -> ExpressionError "Unexpected result from mergeProducts."


-- ============================================================================
-- * Simplification of Sums
-- ============================================================================
simplifySum :: Expression -> ExpressionResult Expression
simplifySum = \case
  Sum [x] -> return x
  Sum xs -> do
      v <- simplifySumStep $ NE.toList xs
      case v of
        []  -> return $ Number 0
        [u] -> return u
        _   -> return $ Sum $ NE.fromList v
  _ -> ExpressionError "Expected a Sum expression"

simplifySumStep :: [Expression] -> ExpressionResult [Expression]
-- length L < 2 does not apply
simplifySumStep [] = return []
simplifySumStep [u] = return [u]

-- Suppose L = [u1, u2] and at least one operand is a sum
simplifySumStep [Sum ps, Sum qs] = mergeSums (NE.toList ps) (NE.toList qs)
simplifySumStep [Sum ps, u2] = mergeSums (NE.toList ps) [u2]
simplifySumStep [u1, Sum qs] = mergeSums [u1] (NE.toList qs)

-- Suppose L = [u1, u2] and neither operand is a product
simplifySumStep [Number 0, u2] = return [u2]
simplifySumStep [u1, Number 0] = return [u1]
simplifySumStep [u1, u2]
  | isConstant u1 && isConstant u2 = do
    p <- simplifyRNE $ Sum [u1, u2]
    case p of
      Number 0 -> return []
      _        -> return [p]
  | getTerm u1 == getTerm u2 = do
    t1 <- getTerm u1
    c1 <- getConst u1
    c0 <- getConst u2
    s <- simplifySum $ Sum [c1, c0]
    p <- simplifyProduct $ Product [s, t1]
    if p == Number 0
      then return []
      else return [p]
  | u2 < u1 = return [u2, u1]
  | otherwise = return [u1, u2]

-- Suppose L = [u1, u2, ..., uN] with N > 2
simplifySumStep (x : xs) = do
  w <- simplifySumStep xs
  case x of
    Sum ps -> mergeSums (NE.toList ps) w
    _      -> mergeSums [x] w

mergeSums :: [Expression] -> [Expression] -> ExpressionResult [Expression]
mergeSums pss [] = return pss
mergeSums [] qss = return qss
mergeSums pss@(p : ps) qss@(q : qs) = do
  h <- simplifySumStep [p, q]
  case h of
    [] -> mergeSums ps qs
    [u] -> do
      rest <- mergeSums ps qs
      return (u : rest)
    [u1, u2] -> if
      | u1 == p && u2 == q -> do
        rest <- mergeSums ps qss
        return (p : rest)
      | u1 == q && u2 == p -> do
        rest <- mergeSums pss qs
        return (q : rest)
      | otherwise -> ExpressionError "Unexpected result from mergeSums"
    _ -> ExpressionError "Unexpected result from mergeSums."

-- ============================================================================
-- * Simplification of Quotients
-- ============================================================================
simplifyQuotient :: Expression -> ExpressionResult Expression
simplifyQuotient = \case
  Quotient u v -> do
    v' <- simplifyPower $ Power v (Number (-1))
    simplifyProduct $ Product [u, v']
  _ -> ExpressionError "Expected a Quotient expression"

-- ============================================================================
-- * Simplification of Differences
-- ============================================================================
simplifyDifference :: Expression -> ExpressionResult Expression
simplifyDifference = \case
  UnaryDifference u -> simplifyProduct $ Product [Number (-1), u]
  BinaryDifference u v -> do
    v' <- simplifyProduct $ Product [Number (-1), v]
    simplifySum $ Sum [u, v']
  _ -> ExpressionError "Expected a Difference expression."

-- ============================================================================
-- * Simplification of Factorial Expressions
-- ============================================================================
simplifyFactorial :: Expression -> ExpressionResult Expression
simplifyFactorial = \case
  Factorial (Number n)
    | n < 0 -> ExpressionUndefined "Factorial of a negative number is undefined"
    | n == 0 -> return $ Number 1
    | otherwise -> return $ Number $ factorial n
  _ -> ExpressionError
    "Expected a Factorial expression with a non-negative integer argument."

-- ============================================================================
-- * Simplification of Functions
-- ============================================================================
simplifyFunction :: Expression -> ExpressionResult Expression
simplifyFunction = \case
  u@(Function _ _) -> return u
  _ -> ExpressionError "Expected a Function expression."
