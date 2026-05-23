-- |
-- Module: SymHask.Symbolic.Basic.Substitution
-- Description: Structural substitution of symbolic expressions
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
--
-- Provides functions for substituting sub-expressions within symbolic expressions.
module SymHask.Symbolic.Basic.Substitution
    ( -- * Wrappers
      Pattern (..)
    , Replacement (..)
      -- * Algorithms
    , concurSubs
    , subs
    ) where

import qualified Data.List.NonEmpty              as NE
import           SymHask.Symbolic
import           SymHask.Symbolic.Simplification ()

-- ============================================================================

-- * Type-Safe Wrappers

-- ============================================================================

-- | What to search for in the expression
newtype Pattern a
  = Pattern { unPattern :: a }
  deriving (Eq, Show)

-- | What to replace the pattern with
newtype Replacement a
  = Replacement { unReplacement :: a }
  deriving (Eq, Show)

-- ============================================================================

-- * Implementation (Internal)

-- ============================================================================

-- | Internal implementation of concurrent substitution
concurSubs ::
  [(Pattern UnsimplifiedExpr, Replacement UnsimplifiedExpr)] ->
  UnsimplifiedExpr ->
  UnsimplifiedExpr
concurSubs equations expr =
  -- First, check if the entire expression matches any pattern
  case findMatchingReplacement expr equations of
    Just replacement -> replacement
    Nothing ->
      -- No direct match, recursively apply to sub-expressions
      case expr of
        Number' n -> mkNumber n
        Fraction' n d -> mkFraction n d
        Symbol' s -> mkSymbol s
        Product' xs -> mkProduct $ NE.map (concurSubs equations) xs
        Sum' xs -> mkSum $ NE.map (concurSubs equations) xs
        Quotient' n d -> mkQuotient (recurse n) (recurse d)
        UnaryDiff' x -> mkUnaryDiff (recurse x)
        BinaryDiff' x y -> mkBinaryDiff (recurse x) (recurse y)
        Power' x y -> mkPower (recurse x) (recurse y)
        Factorial' x -> mkFactorial (recurse x)
        Function' fname args -> mkFunction fname (NE.map (concurSubs equations) args)
 where
  recurse = concurSubs equations

-- | Internal implementation of single substitution
subs :: (Pattern UnsimplifiedExpr, Replacement UnsimplifiedExpr) -> UnsimplifiedExpr -> UnsimplifiedExpr
subs equation@(Pattern pat, Replacement repl) expr
  | expr == pat = repl
  | otherwise = case expr of
      Number' n            -> mkNumber n
      Fraction' n d        -> mkFraction n d
      Symbol' s            -> mkSymbol s
      Product' xs          -> mkProduct $ NE.map recurse xs
      Sum' xs              -> mkSum $ NE.map recurse xs
      Quotient' n d        -> mkQuotient (recurse n) (recurse d)
      UnaryDiff' x         -> mkUnaryDiff (recurse x)
      BinaryDiff' x y      -> mkBinaryDiff (recurse x) (recurse y)
      Power' x y           -> mkPower (recurse x) (recurse y)
      Factorial' x         -> mkFactorial (recurse x)
      Function' fname args -> mkFunction fname (NE.map recurse args)
 where
  recurse = subs equation

-- | Find the first matching replacement for an expression
findMatchingReplacement ::
  Expr a ->
  [(Pattern (Expr a), Replacement (Expr a))] ->
  Maybe (Expr a)
findMatchingReplacement _ [] = Nothing
findMatchingReplacement expr ((Pattern pat, Replacement repl) : rest)
  | expr == pat = Just repl
  | otherwise = findMatchingReplacement expr rest
