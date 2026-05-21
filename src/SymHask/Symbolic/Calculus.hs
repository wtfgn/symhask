{-# LANGUAGE ViewPatterns #-}

module SymHask.Symbolic.Calculus
    ( diff
    , mkDiffVar
    , multiDiff
    ) where

import           Control.Monad                             (foldM)
import           SymHask.Symbolic
import qualified SymHask.Symbolic.Calculus.Differentiation as Differentiation
import           SymHask.Symbolic.Simplification           ()

diff :: SimplifiedExpr -> Differentiation.DiffVar -> EvalResult SimplifiedExpr
diff (unsimplify -> expr) var = do
  diffed <- Differentiation.diff expr var
  simplify diffed

multiDiff :: SimplifiedExpr -> [Differentiation.DiffVar] -> EvalResult SimplifiedExpr
multiDiff = foldM diff

mkDiffVar :: Expr a -> EvalResult Differentiation.DiffVar
mkDiffVar = Differentiation.mkDiffVar
