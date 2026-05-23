{-# LANGUAGE ViewPatterns #-}

-- |
-- Module: SymHask.Symbolic.Calculus
-- Description: Symbolic differentiation and integration of expressions
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
--
-- Support for symbolic differentiation and integration of expressions.
module SymHask.Symbolic.Calculus
    ( -- * Differentiation
      diff
    , mkDiffVar
    , multiDiff
      -- * Integration
    , integrate
    ) where

import           Control.Monad                             (foldM)
import           SymHask.Symbolic
import qualified SymHask.Symbolic.Calculus.Differentiation as Differentiation
import           SymHask.Symbolic.Calculus.Integration     (integrate)
-- | Differentiate a simplified expression with respect to a `DiffVar`.
--
-- >>> let expr = "x"**2 + "y" :: UnsimplifiedExpr
-- >>> let diffVar = mkDiffVar "x"
-- >>> let res = do { expr' <- simplify expr; dv <- diffVar; diff dv expr' }
-- >>> toHaskell <$> res
-- Right "2 * x"
--
-- This could also handle multivariate undefined functions using generalised chain rule. For example:
--
-- \[ \frac{d}{dx} h(x, g(x)) = \frac{\partial h}{\partial x} + \frac{\partial h}{\partial g} \cdot \frac{dg}{dx} \]
--
-- >>> let gx = mkFunction "g" $ NE.singleton "x"
-- >>> let h = mkFunction "h" (NE.fromList ["x", gx])
-- >>> let expr = h :: UnsimplifiedExpr
-- >>> let diffVar = mkDiffVar "x"
-- >>> let res = do { expr' <- simplify expr; dv <- diffVar; diff dv expr' }
-- >>> toHaskell <$> res
-- Right "diff (g x) x * diff (h x (g x)) (g x) + diff (h x (g x)) x"
diff :: Differentiation.DiffVar -> Expr a -> Either ExprError SimplifiedExpr
diff var (unsimplify -> expr) = do
  diffed <- Differentiation.diff expr var
  simplify diffed

-- | Apply `diff` repeatedly for a list of differentiation variables.
--
-- This is useful for computing higher-order derivatives or mixed partial derivatives.
--
-- >>> let expr = "x"**3 * "y"**2 :: UnsimplifiedExpr
-- >>> let diffVars = [mkDiffVar "x", mkDiffVar "y"]
-- >>> let res = do { expr' <- simplify expr; dvs <- sequence diffVars; multiDiff dvs expr' }
-- >>> toHaskell <$> res
-- Right "6 * x ^ 2 * y"
--
-- This could also be used to calculate the second order derivative with respect to x:
--
-- >>> let expr = "x"**3 :: UnsimplifiedExpr
-- >>> let diffVars = replicate 2 (mkDiffVar "x")
-- >>> let res = do { expr' <- simplify expr; dvs <- sequence diffVars; multiDiff dvs expr' }
-- >>> toHaskell <$> res
-- Right "6 * x"
multiDiff :: Foldable t => t Differentiation.DiffVar -> SimplifiedExpr -> Either ExprError SimplifiedExpr
multiDiff vars expr = foldM (flip diff) expr vars

mkDiffVar :: Expr a -> EvalResult Differentiation.DiffVar
mkDiffVar = Differentiation.mkDiffVar
