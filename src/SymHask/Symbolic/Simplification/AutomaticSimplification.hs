{-# LANGUAGE MultiWayIf #-}

module SymHask.Symbolic.Simplification.AutomaticSimplification
    ( automaticSimplify
    ) where

import           SymHask.Symbolic                               (Expression (..),
                                                                 ExpressionResult (..),
                                                                 getConst,
                                                                 getPowerBase,
                                                                 getPowerExponent,
                                                                 getTerm,
                                                                 isConstant,
                                                                 mkDifference,
                                                                 mkFactorial,
                                                                 mkFraction,
                                                                 mkFunction,
                                                                 mkNumber,
                                                                 mkPower,
                                                                 mkProduct,
                                                                 mkQuotient,
                                                                 mkSum)
import           SymHask.Symbolic.Simplification.RationalNumber (simplifyRNE,
                                                                 simplifyRationalNumber)

-- This module is intended to handle automatic simplification of symbolic expressions.
-- ============================================================================

-- ============================================================================
-- * Main Simplification Function
-- ============================================================================
automaticSimplify :: Expression -> ExpressionResult Expression
automaticSimplify = \case
  -- Integers and Symbols are already simplified
  u@(Number _) -> ExpressionSuccess u
  u@(Symbol _) -> ExpressionSuccess u

  -- Fractions are simplified using the rational simplification function
  u@(Fraction _ _) -> simplifyRationalNumber u

  -- Compound expressions are simplified by recursively simplifying their operands
  Power b e -> do
    b' <- automaticSimplify b
    e' <- automaticSimplify e
    simplifyPower $ mkPower b' e'

  Product xs -> do
    xs' <- traverse automaticSimplify xs
    simplifyProduct $ mkProduct xs'

  Sum xs -> do
    xs' <- traverse automaticSimplify xs
    simplifySum $ mkSum xs'

  Quotient u v -> do
    u' <- automaticSimplify u
    v' <- automaticSimplify v
    simplifyQuotient $ mkQuotient u' v'

  Difference xs -> do
    xs' <- traverse automaticSimplify xs
    simplifyDifference $ mkDifference xs'

  Factorial u -> do
    u' <- automaticSimplify u
    simplifyFactorial $ mkFactorial u'

  Function name args -> do
    args' <- traverse automaticSimplify args
    simplifyFunction $ mkFunction name args'

-- ============================================================================
-- * Simplification of Powers
-- ============================================================================
simplifyPower :: Expression -> ExpressionResult Expression
simplifyPower = \case
  -- 0^w = 0, w is a positive integer or fraction
  Power (Number 0) (Number y)
    | y > 0 -> ExpressionSuccess $ mkNumber 0
    | otherwise -> ExpressionUndefined "0 raised to a non-positive power is undefined"
  Power (Number 0) (Fraction n d)
    | n > 0 && d > 0 -> ExpressionSuccess $ mkNumber 0
    | otherwise -> ExpressionUndefined "0 raised to a non-positive power is undefined"

  -- 1^w = 1 for any w
  Power (Number 1) _ -> ExpressionSuccess $ mkNumber 1

  -- v^w = simplifyIntegerPower v w, where w is an integer
  Power v (Number w) -> simplifyIntegerPower v w

  -- If no rules apply, return the expression unchanged
  u -> ExpressionSuccess u

simplifyIntegerPower :: Expression -> Integer -> ExpressionResult Expression
simplifyIntegerPower v@(Number _) n = simplifyRNE $ mkPower v (mkNumber n)
simplifyIntegerPower v@(Fraction _ _) n = simplifyRNE $ mkPower v (mkNumber n)
simplifyIntegerPower _ 0 = ExpressionSuccess $ mkNumber 1
simplifyIntegerPower v 1 = ExpressionSuccess v
simplifyIntegerPower (Power r s) n =
  case simplifyProduct (mkProduct [s, mkNumber n]) of
    ExpressionSuccess (Number p) -> simplifyIntegerPower r p
    ExpressionSuccess p          -> ExpressionSuccess $ mkPower r p
    ExpressionError err          -> ExpressionError err
    ExpressionUndefined msg      -> ExpressionUndefined msg
simplifyIntegerPower (Product xs) n =
  case traverse (`simplifyIntegerPower` n) xs of
    ExpressionSuccess exprs -> simplifyProduct $ mkProduct exprs
    ExpressionError err     -> ExpressionError err
    ExpressionUndefined msg -> ExpressionUndefined msg
simplifyIntegerPower v n = ExpressionSuccess $ mkPower v (mkNumber n)

-- ============================================================================
-- * Simplification of Products
-- ============================================================================
simplifyProduct :: Expression -> ExpressionResult Expression
simplifyProduct = \case
  Product [x] -> ExpressionSuccess x
  Product xs
    | any isZero xs -> ExpressionSuccess $ mkNumber 0
    | otherwise -> do
      v <- simplifyProductStep xs
      case v of
        []  -> ExpressionSuccess $ mkNumber 1
        [u] -> ExpressionSuccess u
        _   -> ExpressionSuccess $ mkProduct v
  _ -> ExpressionError "Expected a Product expression"
  where
    isZero (Number 0) = True
    isZero _          = False

simplifyProductStep :: [Expression] -> ExpressionResult [Expression]
-- length L < 2 does not apply
simplifyProductStep [] = ExpressionSuccess []
simplifyProductStep [u] = ExpressionSuccess [u]

-- Suppose L = [u1, u2] and at least one operand is a product
simplifyProductStep [Product ps, Product qs] = mergeProducts ps qs
simplifyProductStep [Product ps, u2] = mergeProducts ps [u2]
simplifyProductStep [u1, Product qs] = mergeProducts [u1] qs

-- Suppose L = [u1, u2] and neither operand is a product
simplifyProductStep [Number 1, u2] = ExpressionSuccess [u2]
simplifyProductStep [u1, Number 1] = ExpressionSuccess [u1]
simplifyProductStep [u1, u2]
  | isConstant u1 && isConstant u2 = do
    p <- simplifyRNE $ mkProduct [u1, u2]
    case p of
      Number 1 -> ExpressionSuccess []
      _        -> ExpressionSuccess [p]
  | getPowerBase u1 == getPowerBase u2 = do
    b1 <- getPowerBase u1
    e1 <- getPowerExponent u1
    e2 <- getPowerExponent u2
    s <- simplifySum $ mkSum [e1, e2]
    p <- simplifyPower $ mkPower b1 s
    if p == Number 1
      then ExpressionSuccess []
      else ExpressionSuccess [p]
  | u2 < u1 = ExpressionSuccess [u2, u1]
  | otherwise = ExpressionSuccess [u1, u2]

-- Suppose L = [u1, u2, ..., uN] with N > 2
simplifyProductStep (x : xs) = do
  w <- simplifyProductStep xs
  case x of
    Product ps -> mergeProducts ps w
    _          -> mergeProducts [x] w

mergeProducts :: [Expression] -> [Expression] -> ExpressionResult [Expression]
mergeProducts pss [] = ExpressionSuccess pss
mergeProducts [] qss = ExpressionSuccess qss
mergeProducts pss@(p : ps) qss@(q : qs) = do
  h <- simplifyProductStep [p, q]
  case h of
    [] -> mergeProducts ps qs
    [u] -> do
      rest <- mergeProducts ps qs
      ExpressionSuccess (u : rest)
    [u1, u2] -> if
      | u1 == p && u2 == q -> do
        rest <- mergeProducts ps qss
        ExpressionSuccess (p : rest)
      | u1 == q && u2 == p -> do
        rest <- mergeProducts pss qs
        ExpressionSuccess (q : rest)
      | otherwise -> ExpressionError "Unexpected result from mergeProducts"
    _ -> ExpressionError "Unexpected result from mergeProducts."


-- ============================================================================
-- * Simplification of Sums
-- ============================================================================
simplifySum :: Expression -> ExpressionResult Expression
simplifySum = \case
  Sum [x] -> ExpressionSuccess x
  Sum xs -> do
      v <- simplifySumStep xs
      case v of
        []  -> ExpressionSuccess $ mkNumber 0
        [u] -> ExpressionSuccess u
        _   -> ExpressionSuccess $ mkSum v
  _ -> ExpressionError "Expected a Sum expression"

simplifySumStep :: [Expression] -> ExpressionResult [Expression]
-- length L < 2 does not apply
simplifySumStep [] = ExpressionSuccess []
simplifySumStep [u] = ExpressionSuccess [u]

-- Suppose L = [u1, u2] and at least one operand is a sum
simplifySumStep [Sum ps, Sum qs] = mergeSums ps qs
simplifySumStep [Sum ps, u2] = mergeSums ps [u2]
simplifySumStep [u1, Sum qs] = mergeSums [u1] qs

-- Suppose L = [u1, u2] and neither operand is a product
simplifySumStep [Number 0, u2] = ExpressionSuccess [u2]
simplifySumStep [u1, Number 0] = ExpressionSuccess [u1]
simplifySumStep [u1, u2]
  | isConstant u1 && isConstant u2 = do
    p <- simplifyRNE $ mkSum [u1, u2]
    case p of
      Number 0 -> ExpressionSuccess []
      _        -> ExpressionSuccess [p]
  | getTerm u1 == getTerm u2 = do
    t1 <- getTerm u1
    c1 <- getConst u1
    c0 <- getConst u2
    s <- simplifySum $ mkSum [c1, c0]
    p <- simplifyProduct $ mkProduct [s, t1]
    if p == Number 0
      then ExpressionSuccess []
      else ExpressionSuccess [p]
  | u2 < u1 = ExpressionSuccess [u2, u1]
  | otherwise = ExpressionSuccess [u1, u2]

-- Suppose L = [u1, u2, ..., uN] with N > 2
simplifySumStep (x : xs) = do
  w <- simplifySumStep xs
  case x of
    Sum ps -> mergeSums ps w
    _      -> mergeSums [x] w

mergeSums :: [Expression] -> [Expression] -> ExpressionResult [Expression]
mergeSums pss [] = ExpressionSuccess pss
mergeSums [] qss = ExpressionSuccess qss
mergeSums pss@(p : ps) qss@(q : qs) = do
  h <- simplifySumStep [p, q]
  case h of
    [] -> mergeSums ps qs
    [u] -> do
      rest <- mergeSums ps qs
      ExpressionSuccess (u : rest)
    [u1, u2] -> if
      | u1 == p && u2 == q -> do
        rest <- mergeSums ps qss
        ExpressionSuccess (p : rest)
      | u1 == q && u2 == p -> do
        rest <- mergeSums pss qs
        ExpressionSuccess (q : rest)
      | otherwise -> ExpressionError "Unexpected result from mergeSums"
    _ -> ExpressionError "Unexpected result from mergeSums."

-- ============================================================================
-- * Simplification of Quotients
-- ============================================================================
simplifyQuotient :: Expression -> ExpressionResult Expression
simplifyQuotient = \case
  Quotient u v -> do
    v' <- simplifyPower $ mkPower v (mkNumber (-1))
    simplifyProduct $ mkProduct [u, v']
  _ -> ExpressionError "Expected a Quotient expression"

-- ============================================================================
-- * Simplification of Differences
-- ============================================================================
simplifyDifference :: Expression -> ExpressionResult Expression
simplifyDifference = \case
  Difference [u] -> simplifyProduct $ mkProduct [mkNumber (-1), u]
  Difference [u, v] -> do
    v' <- simplifyProduct $ mkProduct [mkNumber (-1), v]
    simplifySum $ mkSum [u, v']
  Difference _ -> ExpressionError "Expected an unary or binary Difference."
  _ -> ExpressionError "Expected a Difference expression."

-- ============================================================================
-- * Simplification of Factorial Expressions
-- ============================================================================
simplifyFactorial :: Expression -> ExpressionResult Expression
simplifyFactorial = \case
  Factorial (Number n)
    | n < 0 -> ExpressionUndefined "Factorial of a negative number is undefined"
    | n == 0 -> ExpressionSuccess $ mkNumber 1
    | otherwise -> ExpressionSuccess $ mkNumber (product [1..n])
  _ -> ExpressionError
    "Expected a Factorial expression with a non-negative integer argument."

-- ============================================================================
-- * Simplification of Functions
-- ============================================================================
simplifyFunction :: Expression -> ExpressionResult Expression
simplifyFunction = \case
  u@(Function _ _) -> ExpressionSuccess u
  _ -> ExpressionError "Expected a Function expression."
