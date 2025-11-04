{-# LANGUAGE ViewPatterns    #-}

module SymHask.Symbolic.Analysis.LinearForm
    ( LinearForm (..)
    , linearForm
    ) where

import           Control.Monad.Error.Class
import qualified Data.List.NonEmpty              as NE
import           Data.Text                       (Text)
import           SymHask.Symbolic
import           SymHask.Symbolic.Analysis.Utils (freeOf)
import           SymHask.Symbolic.Simplification

-- | A linear form represented as a*x + b
data LinearForm
  = LinearForm
      { coeffTerm :: SimplifiedExpr
        -- Coefficient of x
      , constTerm :: SimplifiedExpr
        -- Constant term
      }
  deriving (Eq, Show)

linearForm :: SimplifiedExpr -> Text -> EvalResult (Maybe LinearForm)
linearForm expr (mkSymbol -> x)
  | expr == x =
    pure $ Just $ LinearForm (mkNumber 1) (mkNumber 1)
  | isAtomic expr =
    pure $ Just $ LinearForm (mkNumber 0) expr
  | isProduct expr = analyseProduct expr x
  | isSum expr     = analyseSum expr x
  | freeOf expr x =
    pure $ Just $ LinearForm (mkNumber 0) expr
  | otherwise     = pure Nothing

analyseProduct :: SimplifiedExpr -> SimplifiedExpr -> EvalResult (Maybe LinearForm)
analyseProduct u v
  | freeOf u v = pure $ Just $ LinearForm (mkNumber 0) u
  | otherwise = do
    q <- u ./. v
    if freeOf q v
      then pure $ Just $ LinearForm q (mkNumber 0)
      else pure Nothing

analyseSum :: SimplifiedExpr -> SimplifiedExpr -> EvalResult (Maybe LinearForm)
analyseSum (Sum' tss) (Symbol' v) = do
  let headT = NE.head tss
  restT <- simplify $ mkSum $ NE.fromList (NE.tail tss)
  fstL <- linearForm headT v
  rstL <- linearForm restT v
  case (fstL, rstL) of
    (Just (LinearForm f1 f2), Just (LinearForm r1 r2)) -> do
      newCoeff <- f1 .+. r1
      newConst <- f2 .+. r2
      pure $ Just $ LinearForm newCoeff newConst
    _                    -> pure Nothing
analyseSum _ _ = throwError $ UnsupportedOperation
  "linearForm: analyseSum called with non-sum expression"
