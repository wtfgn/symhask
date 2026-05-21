{-# LANGUAGE ViewPatterns #-}

-- | High-level calculus helpers.
--
-- This module provides convenient wrappers around the lower-level
-- differentiation implementation in
-- `SymHask.Symbolic.Calculus.Differentiation` and ensures results are
-- simplified before returning.
module SymHask.Symbolic.Calculus
    ( -- | Differentiate an expression once with respect to a variable.
      diff
      -- | Create a differentiation variable for the low-level API.
    , mkDiffVar
      -- | Apply multiple successive differentiations.
    , multiDiff
    ) where

import           Control.Monad                             (foldM)
import           SymHask.Symbolic
import qualified SymHask.Symbolic.Calculus.Differentiation as Differentiation
import           SymHask.Symbolic.Simplification           ()

diff :: SimplifiedExpr -> Differentiation.DiffVar -> EvalResult SimplifiedExpr
-- | Differentiate a simplified expression with respect to a `DiffVar`.
-- The result is simplified before being returned.
diff (unsimplify -> expr) var = do
  diffed <- Differentiation.diff expr var
  simplify diffed

-- | Apply `diff` repeatedly for a list of differentiation variables.
multiDiff :: SimplifiedExpr -> [Differentiation.DiffVar] -> EvalResult SimplifiedExpr
multiDiff = foldM diff

mkDiffVar :: Expr a -> EvalResult Differentiation.DiffVar
mkDiffVar = Differentiation.mkDiffVar
