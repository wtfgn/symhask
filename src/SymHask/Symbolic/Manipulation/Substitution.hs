{-# LANGUAGE ViewPatterns #-}

module SymHask.Symbolic.Manipulation.Substitution
    ( -- * Wrappers
      Pattern (..)
    , Replacement (..)
      -- * With Simplification
    , concurSubs
    , seqSubs
    , subs
      -- * Structural Substitution (Based on the AST)
    , concurSubsStruct
    , seqSubsStruct
    , subsStruct
    ) where

import           Data.List                            (foldl')
import qualified Data.List.NonEmpty                   as NE
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
-- * Semantic Substitution (Simplified Only)
-- ============================================================================

-- | Substitution with simplification
subs
  :: (Pattern SimplifiedExpr, Replacement SimplifiedExpr)
  -> SimplifiedExpr
  -> EvalResult SimplifiedExpr
subs
  (unsimplify . unPattern -> pat, unsimplify . unReplacement -> repl)
  (unsimplify -> expr) =
    simplify $ subsImpl (Pattern pat, Replacement repl) expr


seqSubs
  :: [(Pattern SimplifiedExpr, Replacement SimplifiedExpr)]
  -> SimplifiedExpr
  -> EvalResult SimplifiedExpr
seqSubs [] expr = pure expr
seqSubs ((p, r) : rest) expr = do
  result <- subs (p, r) expr
  seqSubs rest result

-- | Concurrent semantic substitution (with simplification)
concurSubs
  :: [(Pattern SimplifiedExpr, Replacement SimplifiedExpr)]
  -> SimplifiedExpr
  -> EvalResult SimplifiedExpr
concurSubs equations (unsimplify -> expr) = do
  let structuralEquations = [(Pattern (unsimplify $ unPattern p),
                             Replacement (unsimplify $ unReplacement r))
                            | (p, r) <- equations]
  let result = concurSubsImpl structuralEquations expr
  simplify result

-- ============================================================================
-- * Structural Substitution (Unrestricted)
-- ============================================================================

-- | Structural substitution - exact pattern matching
subsStruct :: (Pattern UnsimplifiedExpr, Replacement UnsimplifiedExpr) -> UnsimplifiedExpr -> UnsimplifiedExpr
subsStruct = subsImpl

-- | Multiple structural substitutions
seqSubsStruct
  :: [(Pattern UnsimplifiedExpr, Replacement UnsimplifiedExpr)]
  -> UnsimplifiedExpr
  -> UnsimplifiedExpr
seqSubsStruct rest expr = foldl' (flip subsStruct) expr rest

-- | Concurrent structural substitution - all patterns matched against original expression
--
-- Given expression u and set S = {t1 = r1, t2 = r2, ..., tn = rn},
-- recursively search through u and for each sub-expression v:
-- if v is identical to some ti, substitute ri for v.
-- All substitutions happen based on the original expression structure.
concurSubsStruct
  :: [(Pattern UnsimplifiedExpr, Replacement UnsimplifiedExpr)]  -- ^ Set S of equations {ti = ri}
  -> UnsimplifiedExpr                                   -- ^ Expression u
  -> UnsimplifiedExpr
concurSubsStruct = concurSubsImpl

-- ============================================================================
-- * Implementation (Internal)
-- ============================================================================

subsImpl :: (Pattern UnsimplifiedExpr, Replacement UnsimplifiedExpr) -> UnsimplifiedExpr -> UnsimplifiedExpr
subsImpl equation@(Pattern pat, Replacement repl) expr
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
    recurse = subsImpl equation


-- | Internal implementation of concurrent substitution
concurSubsImpl
  :: [(Pattern UnsimplifiedExpr, Replacement UnsimplifiedExpr)]
  -> UnsimplifiedExpr
  -> UnsimplifiedExpr
concurSubsImpl equations expr =
  -- First, check if the entire expression matches any pattern
  case findMatchingReplacement expr equations of
    Just replacement -> replacement
    Nothing ->
      -- No direct match, recursively apply to sub-expressions
      case expr of
        Number' n            -> mkNumber n
        Fraction' n d        -> mkFraction n d
        Symbol' s            -> mkSymbol s
        Product' xs          -> mkProduct $ NE.map (concurSubsImpl equations) xs
        Sum' xs              -> mkSum $ NE.map (concurSubsImpl equations) xs
        Quotient' n d        -> mkQuotient (recurse n) (recurse d)
        UnaryDiff' x         -> mkUnaryDiff (recurse x)
        BinaryDiff' x y      -> mkBinaryDiff (recurse x) (recurse y)
        Power' x y           -> mkPower (recurse x) (recurse y)
        Factorial' x         -> mkFactorial (recurse x)
        Function' fname args -> mkFunction fname (NE.map (concurSubsImpl equations) args)
  where
    recurse = concurSubsImpl equations

-- | Find the first matching replacement for an expression
findMatchingReplacement
  :: Expr s
  -> [(Pattern (Expr s), Replacement (Expr s))]
  -> Maybe (Expr s)
findMatchingReplacement _ [] = Nothing
findMatchingReplacement expr ((Pattern pat, Replacement repl):rest)
  | expr == pat = Just repl
  | otherwise = findMatchingReplacement expr rest
