{-# LANGUAGE MultiWayIf #-}

-- |
-- Module: SymHask.Symbolic.Simplification.AutomaticSimplification
-- Description: Internal module for automatic simplification of symbolic expressions
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
--
module SymHask.Symbolic.Simplification.AutomaticSimplification
    ( automaticSimplify
    ) where

import           Control.Monad.Error.Class                      (throwError)
import           Data.Either                                    (fromRight)
import           Data.List.NonEmpty                             (NonEmpty ((:|)))
import qualified Data.List.NonEmpty                             as NE
import           Data.Text                                      (Text)
import           Math.Combinatorics.Exact.Factorial             (factorial)
import           SymHask.Symbolic
import           SymHask.Symbolic.Simplification.RationalNumber (simplifyRNE,
                                                                 toStandardRNE)

-- ============================================================================

-- * Main Simplification Function

-- ============================================================================
-- | Internal function that performs automatic simplification
--
-- Most operators required the input to be in simplified form,
-- as they rely on the properties of simplified expressions.
--
-- Note: This function is not intended to be used directly by users.
-- Instead, it is called by the `simplify` method of the `Simplify` type class.
automaticSimplify :: Expr a -> EvalResult UnsimplifiedExpr
automaticSimplify = \case
  -- Integers and Symbols are already simplified
  Number' n -> pure $ mkNumber n
  Symbol' s -> pure $ mkSymbol s
  -- Fractions are simplified using the rational simplification function
  Fraction' n d -> toStandardRNE (mkFraction n d)
  -- Compound expressions are simplified by recursively simplifying their operands
  Power' b e -> do
    b' <- automaticSimplify b
    e' <- automaticSimplify e
    simplifyPower $ mkPower b' e'
  Product' xs -> do
    xs' <- traverse automaticSimplify xs
    simplifyProduct $ mkProduct xs'
  Sum' xs -> do
    xs' <- traverse automaticSimplify xs
    simplifySum $ mkSum xs'
  Quotient' u v -> simplifyQuotient (mkQuotient u v)
  UnaryDiff' u -> simplifyUnaryDiff (mkUnaryDiff u)
  BinaryDiff' u v -> simplifyBinaryDiff (mkBinaryDiff u v)
  Factorial' u -> simplifyFactorial (mkFactorial u)
  Function' fname args -> simplifyFunction fname args

-- ============================================================================

-- * Simplification of Powers

-- ============================================================================
simplifyPower :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
simplifyPower = \case
  -- 0^w = 0, w is a positive integer or fraction
  Power' (Number' 0) (Number' y)
    | y > 0 -> pure $ mkNumber 0
    | otherwise ->
        throwError $
          InvalidDomain "0 raised to a non-positive power is undefined"
  Power' (Number' 0) (Fraction' n d)
    | n > 0 && d > 0 -> pure $ mkNumber 0
    | otherwise ->
        throwError $
          InvalidDomain "0 raised to a non-positive power is undefined"
  -- 1^w = 1 for any w
  Power' (Number' 1) _ -> pure $ mkNumber 1
  -- v^w = simplifyIntegerPower v w, where w is an integer
  Power' v (Number' w) -> simplifyIntegerPower v w
  -- If no rules apply, return the expression unchanged
  u -> pure u

simplifyIntegerPower :: UnsimplifiedExpr -> Integer -> EvalResult UnsimplifiedExpr
simplifyIntegerPower (Number' k) n =
  simplifyRNE (mkPower (mkNumber k) (mkNumber n))
simplifyIntegerPower (Fraction' num denom) n =
  simplifyRNE (mkPower (mkFraction num denom) (mkNumber n))
simplifyIntegerPower _ 0 = pure $ mkNumber 1
simplifyIntegerPower v 1 = pure v
simplifyIntegerPower (Power' r s) n =
  case simplifyProduct (mkProduct (s :| [mkNumber n])) of
    Right (Number' p) -> simplifyIntegerPower r p
    Right p           -> pure $ mkPower r p
    Left err          -> Left err
simplifyIntegerPower (Product' xs) n =
  case traverse (`simplifyIntegerPower` n) xs of
    Right exprs -> simplifyProduct $ mkProduct exprs
    Left err    -> Left err
simplifyIntegerPower v n = pure $ mkPower v (mkNumber n)

-- ============================================================================

-- * Simplification of Products

-- ============================================================================
simplifyProduct :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
simplifyProduct = \case
  Product' (x :| []) -> pure x
  Product' xs
    | any isZero xs -> pure $ mkNumber 0
    | otherwise -> do
        v <- simplifyProductStep $ NE.toList xs
        case v of
          []  -> pure $ mkNumber 1
          [u] -> pure u
          _   -> return $ mkProduct $ NE.fromList v
  _ -> throwError $ UnsupportedOperation "Expected a Product expression"
 where
  isZero (Number' 0) = True
  isZero _           = False

-- length L < 2 does not apply
simplifyProductStep :: [UnsimplifiedExpr] -> EvalResult [UnsimplifiedExpr]
simplifyProductStep [] = return []
simplifyProductStep [u] = return [u]
-- Suppose L = [u1, u2] and at least one operand is a product
simplifyProductStep [Product' ps, Product' qs] =
  mergeProducts (NE.toList ps) (NE.toList qs)
simplifyProductStep [Product' ps, u2] =
  mergeProducts (NE.toList ps) [u2]
simplifyProductStep [u1, Product' qs] =
  mergeProducts [u1] (NE.toList qs)
-- Suppose L = [u1, u2] and neither operand is a product
simplifyProductStep [Number' 1, u2] = return [u2]
simplifyProductStep [u1, Number' 1] = return [u1]
simplifyProductStep [Number' n1, Number' n2] = simplifyProductConst (mkNumber n1) (mkNumber n2)
simplifyProductStep [Number' n1, Fraction' num denom] = simplifyProductConst (mkNumber n1) (mkFraction num denom)
simplifyProductStep [Fraction' num denom, Number' n2] = simplifyProductConst (mkFraction num denom) (mkNumber n2)
simplifyProductStep [Fraction' n1 d1, Fraction' n2 d2] = simplifyProductConst (mkFraction n1 d1) (mkFraction n2 d2)
simplifyProductStep [u1, u2]
  | getBase u1 == getBase u2 = do
      b1 <- getBase u1
      e1 <- getExponent u1
      e2 <- getExponent u2
      s <- simplifySum $ mkSum (e1 :| [e2])
      p <- simplifyPower $ mkPower b1 s
      if p == mkNumber 1 then return [] else return [p]
  | u2 <. u1 = return [u2, u1]
  | otherwise = return [u1, u2]
-- Suppose L = [u1, u2, ..., uN] with N > 2
simplifyProductStep (x : xs) = do
  w <- simplifyProductStep xs
  case x of
    Product' ps -> mergeProducts (NE.toList ps) w
    _           -> mergeProducts [x] w

simplifyProductConst :: UnsimplifiedExpr -> UnsimplifiedExpr -> EvalResult [UnsimplifiedExpr]
simplifyProductConst c1 c2 =
  simplifyRNE (mkProduct (c1 :| [c2]))
    >>= ( \case
            Number' 1 -> return []
            p -> return [p]
        )

mergeProducts :: [UnsimplifiedExpr] -> [UnsimplifiedExpr] -> EvalResult [UnsimplifiedExpr]
mergeProducts pss [] = return pss
mergeProducts [] qss = return qss
mergeProducts pss@(p : ps) qss@(q : qs) = do
  h <- simplifyProductStep [p, q]
  case h of
    [] -> mergeProducts ps qs
    [u] -> do
      rest <- mergeProducts ps qs
      return (u : rest)
    [u1, u2] ->
      if
        | u1 == p && u2 == q -> do
            rest <- mergeProducts ps qss
            return (p : rest)
        | u1 == q && u2 == p -> do
            rest <- mergeProducts pss qs
            return (q : rest)
        | otherwise ->
            throwError $
              EvaluationFailure "Unexpected result from mergeProducts"
    _ ->
      throwError $
        EvaluationFailure "Unexpected result from mergeProducts."

-- ============================================================================

-- * Simplification of Sums

-- ============================================================================
simplifySum :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
simplifySum = \case
  Sum' (x :| []) -> pure x
  Sum' xs ->
    simplifySumStep (NE.toList xs)
      >>= ( \case
              [] -> return $ mkNumber 0
              [u] -> return u
              v -> return $ mkSum $ NE.fromList v
          )
  _ -> throwError $ UnsupportedOperation "Expected a Sum expression"

simplifySumStep :: [UnsimplifiedExpr] -> EvalResult [UnsimplifiedExpr]
-- length L < 2 does not apply
simplifySumStep [] = pure []
simplifySumStep [u] = pure [u]
-- Suppose L = [u1, u2] and at least one operand is a sum
simplifySumStep [Sum' ps, Sum' qs] = mergeSums (NE.toList ps) (NE.toList qs)
simplifySumStep [Sum' ps, u2] = mergeSums (NE.toList ps) [u2]
simplifySumStep [u1, Sum' qs] = mergeSums [u1] (NE.toList qs)
-- Suppose L = [u1, u2] and neither operand is a product
simplifySumStep [Number' 0, u2] = pure [u2]
simplifySumStep [u1, Number' 0] = pure [u1]
simplifySumStep [Number' n1, Number' n2] = simplifySumConst (mkNumber n1) (mkNumber n2)
simplifySumStep [Number' n1, Fraction' num denom] = simplifySumConst (mkNumber n1) (mkFraction num denom)
simplifySumStep [Fraction' num denom, Number' n2] = simplifySumConst (mkFraction num denom) (mkNumber n2)
simplifySumStep [Fraction' n1 d1, Fraction' n2 d2] = simplifySumConst (mkFraction n1 d1) (mkFraction n2 d2)
simplifySumStep [u1, u2]
  | getTerm u1 == getTerm u2 = do
      t1 <- getTerm u1
      c1 <- getConst u1
      c0 <- getConst u2
      s <- simplifySum $ mkSum (c1 :| [c0])
      p <- simplifyProduct $ mkProduct (s :| [t1])
      if p == mkNumber 0 then return [] else return [p]
  | u2 <. u1 = return [u2, u1]
  | otherwise = return [u1, u2]
-- Suppose L = [u1, u2, ..., uN] with N > 2
simplifySumStep (x : xs) = do
  w <- simplifySumStep xs
  case x of
    Sum' ps -> mergeSums (NE.toList ps) w
    _       -> mergeSums [x] w

simplifySumConst :: UnsimplifiedExpr -> UnsimplifiedExpr -> EvalResult [UnsimplifiedExpr]
simplifySumConst c1 c2 =
  simplifyRNE (mkSum (c1 :| [c2]))
    >>= ( \case
            Number' 0 -> return []
            p -> return [p]
        )

mergeSums :: [UnsimplifiedExpr] -> [UnsimplifiedExpr] -> EvalResult [UnsimplifiedExpr]
mergeSums pss [] = return pss
mergeSums [] qss = return qss
mergeSums pss@(p : ps) qss@(q : qs) = do
  h <- simplifySumStep [p, q]
  case h of
    [] -> mergeSums ps qs
    [u] -> do
      rest <- mergeSums ps qs
      return (u : rest)
    [u1, u2] ->
      if
        | u1 == p && u2 == q -> do
            rest <- mergeSums ps qss
            return (p : rest)
        | u1 == q && u2 == p -> do
            rest <- mergeSums pss qs
            return (q : rest)
        | otherwise -> throwError $ EvaluationFailure "Unexpected result from mergeSums"
    _ -> throwError $ EvaluationFailure "Unexpected result from mergeSums."

-- ============================================================================

-- * Simplification of Quotients

-- ============================================================================
simplifyQuotient :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
simplifyQuotient (Quotient' u v) = do
  u' <- automaticSimplify u
  v' <- automaticSimplify v
  recipV <- simplifyPower $ mkPower v' (mkNumber (-1))
  simplifyProduct $ mkProduct (u' :| [recipV])
simplifyQuotient _ = throwError $ UnsupportedOperation "Expected a Quotient expression"

-- ============================================================================

-- * Simplification of Differences

-- ============================================================================
simplifyUnaryDiff :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
simplifyUnaryDiff (UnaryDiff' u) = do
  u' <- automaticSimplify u
  simplifyProduct $ mkProduct (mkNumber (-1) :| [u'])
simplifyUnaryDiff _ = throwError $ UnsupportedOperation "Expected a UnaryDiff expression"

simplifyBinaryDiff :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
simplifyBinaryDiff (BinaryDiff' u v) = do
  u' <- automaticSimplify u
  v' <- automaticSimplify v
  negV <- simplifyProduct $ mkProduct (mkNumber (-1) :| [v'])
  simplifySum $ mkSum (u' :| [negV])
simplifyBinaryDiff _ = throwError $ UnsupportedOperation "Expected a BinaryDiff expression"

-- ============================================================================

-- * Simplification of Factorial Expressions

-- ============================================================================
simplifyFactorial :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
simplifyFactorial (Factorial' u) = do
  u' <- automaticSimplify u
  case u' of
    Number' n
      | n < 0 -> throwError $ InvalidDomain "Factorial of a negative number is undefined"
      | n == 0 -> return $ mkNumber 1
      | otherwise -> return $ mkNumber $ factorial $ fromIntegral n
    _ -> return $ mkFactorial u'
simplifyFactorial _ = throwError $ UnsupportedOperation "Expected a Factorial expression"

-- ============================================================================

-- * Simplification of Functions

-- ============================================================================
simplifyFunction :: Text -> NonEmpty (Expr a) -> EvalResult UnsimplifiedExpr
simplifyFunction fname args = do
  args' <- traverse automaticSimplify args
  return $ mkFunction fname args'

-- ============================================================================

-- * Order Relation for Algebraic Expressions

-- ============================================================================

infix 4 <.
(<.) :: UnsimplifiedExpr -> UnsimplifiedExpr -> Bool
-- Compare constants
(<.) (Number' n1) (Number' n2) = n1 < n2
(<.) (Fraction' n1 d1) (Fraction' n2 d2) = n1 * d2 < n2 * d1
(<.) (Number' x) (Fraction' n d) = x * d < n
(<.) (Fraction' n d) (Number' x) = n < x * d
-- Compare symbols (lexicographically)
(<.) (Symbol' s1) (Symbol' s2) = s1 < s2
-- Compare products and sums by their operands [u_1, ..., u_m] and [v_1, ..., v_n]
-- start comparing with the most significant operand u_m and v_n
(<.) (Product' xs1) (Product' xs2) = compareOperands (NE.reverse xs1) (NE.reverse xs2)
(<.) (Sum' xs1) (Sum' xs2) = compareOperands (NE.reverse xs1) (NE.reverse xs2)
-- Compare powers by base and exponent
(<.) u@(Power' _ _) v@(Power' _ _) =
  fromRight False $ do
    b1 <- getBase u
    b2 <- getBase v
    e1 <- getExponent u
    e2 <- getExponent v
    return $ if b1 == b2 then e1 <. e2 else b1 <. b2

-- Compare factorials
(<.) (Factorial' u1) (Factorial' u2) = u1 <. u2
-- Compare functions by name and arguments
-- The most significant arguments for functions are the first operands
(<.) (Function' f1 args1) (Function' f2 args2) =
  if f1 == f2 then compareOperands args1 args2 else f1 < f2
-- Compare when one is an integer or fraction and the other is any other type
-- This ensures constant must be the first operand
(<.) (Number' _) _ = True
(<.) (Fraction' _ _) _ = True
-- Compare when one is a product and the other
-- is a power, sum, factorial, function or symbol
(<.) u@(Product' _) v@(Power' _ _) = u <. mkProduct (NE.singleton v)
(<.) u@(Product' _) v@(Sum' _) = u <. mkProduct (NE.singleton v)
(<.) u@(Product' _) v@(Factorial' _) = u <. mkProduct (NE.singleton v)
(<.) u@(Product' _) v@(Function' _ _) = u <. mkProduct (NE.singleton v)
(<.) u@(Product' _) v@(Symbol' _) = u <. mkProduct (NE.singleton v)
-- Compare when one is a power and the other
-- is a sum, factorial, function, or symbol
(<.) u@(Power' _ _) v@(Sum' _) = u <. mkPower v (mkNumber 1)
(<.) u@(Power' _ _) v@(Factorial' _) = u <. mkPower v (mkNumber 1)
(<.) u@(Power' _ _) v@(Function' _ _) = u <. mkPower v (mkNumber 1)
(<.) u@(Power' _ _) v@(Symbol' _) = u <. mkPower v (mkNumber 1)
-- Compare when one is a sum and the other is a factorial, function, or symbol
(<.) u@(Sum' _) v@(Factorial' _) = u <. mkSum (NE.singleton v)
(<.) u@(Sum' _) v@(Function' _ _) = u <. mkSum (NE.singleton v)
(<.) u@(Sum' _) v@(Symbol' _) = u <. mkSum (NE.singleton v)
-- Compare when one is a factorial and the other is a function or symbol
(<.) u@(Factorial' x) v@(Function' _ _) = x /= v && u <. mkFactorial v
(<.) u@(Factorial' x) v@(Symbol' _) = x /= v && u <. mkFactorial v
-- Compare when one is a function and the other is a symbol
(<.) u@(Function' f _) v@(Symbol' s) = u /= v && f < s
-- If all else fails, reverse the comparison
-- This ensures a total order even for mixed types
(<.) u v = not (v <. u)

compareOperands :: NonEmpty UnsimplifiedExpr -> NonEmpty UnsimplifiedExpr -> Bool
compareOperands xs ys = compareOperands' (NE.toList xs) (NE.toList ys)
 where
  compareOperands' [] [] = False -- Equal lists
  compareOperands' [] (_ : _) = True -- First shorter
  compareOperands' (_ : _) [] = False -- Second shorter
  compareOperands' (x : xs') (y : ys') =
    if x == y then compareOperands' xs' ys' else x <. y

-- ============================================================================

-- * Helper Functions to Extract Parts of Expressions

-- ============================================================================

getBase :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
getBase = \case
  Symbol' s -> pure $ mkSymbol s
  Product' xs -> pure $ mkProduct xs
  Sum' xs -> pure $ mkSum xs
  Factorial' x -> pure $ mkFactorial x
  Function' fname args -> pure $ mkFunction fname args
  Power' b _ -> pure b
  Number' _ ->
    throwError $
      UnsupportedOperation "Cannot extract base from integer"
  Fraction' _ _ ->
    throwError $
      UnsupportedOperation "Cannot extract base from fraction"
  _ ->
    throwError $
      UnsupportedOperation "Cannot extract base from this expression"

getExponent :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
getExponent = \case
  Symbol' _ -> pure $ mkNumber 1
  Product' _ -> pure $ mkNumber 1
  Sum' _ -> pure $ mkNumber 1
  Factorial' _ -> pure $ mkNumber 1
  Function' _ _ -> pure $ mkNumber 1
  Power' _ e -> pure e
  Number' _ ->
    throwError $
      UnsupportedOperation "Cannot extract exponent from integer"
  Fraction' _ _ ->
    throwError $
      UnsupportedOperation "Cannot extract exponent from fraction"
  _ ->
    throwError $
      UnsupportedOperation "Cannot extract exponent from this expression"

getTerm :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
getTerm = \case
  u@(Symbol' _) -> pure . mkProduct . NE.singleton $ u
  u@(Sum' _) -> pure . mkProduct . NE.singleton $ u
  u@(Power' _ _) -> pure . mkProduct . NE.singleton $ u
  u@(Factorial' _) -> pure . mkProduct . NE.singleton $ u
  u@(Function' _ _) -> pure . mkProduct . NE.singleton $ u
  u@(Product' (x :| xs)) ->
    pure $
      if isConstant x
        then mkProduct $ NE.fromList xs
        else u
  Number' _ ->
    throwError $
      UnsupportedOperation "Cannot extract terms from integer"
  Fraction' _ _ ->
    throwError $
      UnsupportedOperation "Cannot extract terms from fraction"
  _ ->
    throwError $
      UnsupportedOperation "Cannot extract terms from this expression"

getConst :: UnsimplifiedExpr -> EvalResult UnsimplifiedExpr
getConst = \case
  Symbol' _ -> pure $ mkNumber 1
  Sum' _ -> pure $ mkNumber 1
  Power' _ _ -> pure $ mkNumber 1
  Factorial' _ -> pure $ mkNumber 1
  Function' _ _ -> pure $ mkNumber 1
  Product' (x :| _) -> pure $ if isConstant x then x else mkNumber 1
  Number' _ ->
    throwError $
      UnsupportedOperation "Cannot extract constant from integer"
  Fraction' _ _ ->
    throwError $
      UnsupportedOperation "Cannot extract constant from fraction"
  _ ->
    throwError $
      UnsupportedOperation "Cannot extract constant from this expression"
