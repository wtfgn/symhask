{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}

module SymHask.Symbolic.Calculus.Differentiation
    ( DiffVar
    , diff
    , mkDiffVar
    ) where

import           Control.Monad.Error.Class       (MonadError (throwError))
import           Data.List.NonEmpty              (NonEmpty ((:|)))
import qualified Data.List.NonEmpty              as NE
import           Data.Text                       (Text)
import           SymHask.Symbolic
import           SymHask.Symbolic.Basic          (freeOf)
import           SymHask.Symbolic.Simplification ()

-- ============================================================================
-- * Data Types
-- ============================================================================

data DiffVar
  = DiffSymbol Text -- Variable symbol
  | DiffFunction Text (NE.NonEmpty Text) -- Undefined functions
  deriving (Eq, Show)

-- pattern Diff' :: SimplifiedExpr -> SimplifiedExpr -> SimplifiedExpr
-- pattern Diff' expr x <- Function' "diff" (expr :| [x])

-- ============================================================================
-- * Helpers
-- ============================================================================

diffVarToExpr :: DiffVar -> Expr a
diffVarToExpr (DiffSymbol s) = mkSymbol s
diffVarToExpr (DiffFunction fname args) =
  let args' = NE.fromList $ map mkSymbol (NE.toList args)
  in mkFunction fname args'

mkDiffExpr :: Expr a -> DiffVar -> Expr a
mkDiffExpr expr (diffVarToExpr -> var) = mkFunction "diff" (expr :| [var])

mkDiffVar :: Expr s -> EvalResult DiffVar
mkDiffVar (Symbol' s) = pure $ DiffSymbol s
mkDiffVar (Function' fname args) =
  let argNames = [ s | Symbol' s <- NE.toList args ]
  in pure $ DiffFunction fname (NE.fromList argNames)
mkDiffVar _ = throwError $
  UnsupportedOperation "Cannot create DiffVar from this expression type"

-- ============================================================================
-- * Implementation
-- ============================================================================

diff :: UnsimplifiedExpr -> DiffVar -> EvalResult UnsimplifiedExpr
diff expr dVar@(unsimplify . diffVarToExpr -> var) = case expr of
  _ | expr == var -> pure $ mkNumber 1
  Power' v w -> powerRule v w dVar
  Sum' terms -> sumRule terms dVar
  Product' factors -> productRule factors dVar
  Function' _ _ -> functionRule expr dVar
  _ -> do
    expr' <- simplify expr
    var' <- simplify var
    if freeOf expr' var'
      then return $ mkNumber 0
      else return $ unsimplify $ mkDiffExpr expr dVar

powerRule :: UnsimplifiedExpr -> UnsimplifiedExpr -> DiffVar -> EvalResult UnsimplifiedExpr
powerRule b e dVar = do
  db <- diff b dVar
  de <- diff e dVar
  return $ e * (b ** (e - mkNumber 1)) * db + de * (b ** e) * log b

sumRule :: NE.NonEmpty UnsimplifiedExpr -> DiffVar -> EvalResult UnsimplifiedExpr
sumRule terms dVar = do
  diffs <- mapM (`diff` dVar) terms
  return $ mkSum diffs

productRule :: NE.NonEmpty UnsimplifiedExpr -> DiffVar -> EvalResult UnsimplifiedExpr
productRule factors dVar = do
  let factorList = NE.toList factors
  terms <- traverse (productTerm factorList dVar) [0..length factorList - 1]
  pure $ sum $ filter (/= 0) terms
  where
    productTerm fs var i = do
      deriv <- diff (fs !! i) var
      let others = take i fs <> drop (i + 1) fs
      pure $ deriv * product others

functionRule :: UnsimplifiedExpr -> DiffVar -> EvalResult UnsimplifiedExpr
functionRule (Sqrt' v) x = do
  dv <- diff v x
  pure $ (1 / (2 * sqrt v)) * dv

functionRule (Exp' v) x = do
  dv <- diff v x
  pure $ exp v * dv

functionRule (LogBase' b v) x = do
  dv <- diff v x
  db <- diff b x
  pure $ dv / (v * log b) - db * log v / (b * log b ** 2)

functionRule (Log' v) x = do
  dv <- diff v x
  pure $ dv / v

functionRule (Sin' v) x = do
  dv <- diff v x
  pure $ cos v * dv

functionRule (Cos' v) x = do
  dv <- diff v x
  pure $ - (sin v * dv)

functionRule (Tan' v) x = do
  dv <- diff v x
  pure $ (1 / cos v) ** 2 * dv

functionRule (Cot' v) x =do
  dv <- diff v x
  pure $ - ((1 / sin v) ** 2 * dv)

functionRule (Sec' v) x = do
  dv <- diff v x
  pure (sin v / cos v ** 2 * dv)

functionRule (Csc' v) x = do
  dv <- diff v x
  pure $ - (cos v / sin v ** 2 * dv)

functionRule (Asin' v) x = do
  dv <- diff v x
  pure $ 1 / sqrt (1 - v ** 2) * dv

functionRule (Acos' v) x = do
  dv <- diff v x
  pure $ - (1 / sqrt (1 - v ** 2) * dv)

functionRule (Atan' v) x = do
  dv <- diff v x
  pure $ 1 / (1 + v ** 2) * dv

functionRule (Acot' v) x = do
  dv <- diff v x
  pure $ - (1 / (1 + v ** 2) * dv)

functionRule (Asec' v) x = do
  dv <- diff v x
  pure $ 1 / (abs v * sqrt (v ** 2 - 1)) * dv

functionRule (Acsc' v) x = do
  dv <- diff v x
  pure $ - (1 / (abs v * sqrt (v ** 2 - 1)) * dv)

functionRule (Sinh' v) x = do
  dv <- diff v x
  pure $ cosh v * dv

functionRule (Cosh' v) x = do
  dv <- diff v x
  pure $ sinh v * dv

functionRule (Tanh' v) x = do
  dv <- diff v x
  pure $ 1 / cosh v ** 2 * dv

functionRule (Coth' v) x = do
  dv <- diff v x
  pure $ - (1 / sinh v ** 2 * dv)

functionRule (Sech' v) x = do
  dv <- diff v x
  pure $ - (sinh v / cosh v ** 2 * dv)

functionRule (Csch' v) x = do
  dv <- diff v x
  pure $ - (cosh v / sinh v ** 2 * dv)

functionRule (Asinh' v) x = do
  dv <- diff v x
  pure $ 1 / sqrt (v ** 2 + 1) * dv

functionRule (Acosh' v) x = do
  dv <- diff v x
  pure $ 1 / sqrt (v ** 2 - 1) * dv

functionRule (Atanh' v) x = do
  dv <- diff v x
  pure $ 1 / (1 - v ** 2) * dv

functionRule (ACoth' v) x = do
  dv <- diff v x
  pure $ 1 / (1 - v ** 2) * dv

functionRule (ASech' v) x = do
  dv <- diff v x
  pure $ - (1 / (v * sqrt (1 - v ** 2)) * dv)

functionRule (ACsch' v) x = do
  dv <- diff v x
  pure $ - (1 / (abs v * sqrt (1 + v ** 2)) * dv)

-- Unknown functions - apply generalized chain rule
-- d/dx f(u₁, u₂, ..., uₙ) = Σᵢ (∂f/∂uᵢ) * (duᵢ/dx)
functionRule (Function' fname args) dVar = do
  chainTerms <- traverse (argTerm fname args dVar) args
  return $ sum $ NE.filter (/= 0) chainTerms
  where
    argTerm funcName allArgs var arg = do
      argDiff <- diff arg var
      if argDiff == 0
        then return 0
        else do
          argVar <- mkDiffVar arg
          let partial = mkDiffExpr (mkFunction funcName allArgs) argVar
          return $ partial * argDiff

functionRule _ _ = throwError $ UnsupportedOperation
  "Unsupported function type for differentiation."
