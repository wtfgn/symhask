{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tan" #-}

module SymHask.Symbolic.Trigonometry
    (
    ) where

import           SymHask.Symbolic                                        (Expression (..),
                                                                          ExpressionResult,
                                                                          pattern Cos',
                                                                          pattern Cot',
                                                                          pattern Csc',
                                                                          pattern Sec',
                                                                          pattern Sin',
                                                                          pattern Tan')
import           SymHask.Symbolic.Simplification.AutomaticSimplification (automaticSimplify)

-- ============================================================================
-- Trigonometric Substitutions
-- ============================================================================
-- Returns a new expressions where all instances of the functions
-- tan, cot, sec, and csc are replaced by the representations
-- using sin and cos
trigSubstitute :: Expression -> ExpressionResult Expression
trigSubstitute u = do
  u' <- automaticSimplify u
  u'' <- applyTrigSubstitutionRules u'
  automaticSimplify u''

-- Assume the expression is already simplified
applyTrigSubstitutionRules :: Expression -> ExpressionResult Expression
applyTrigSubstitutionRules = \case
    -- atomic expressions
    u'@(Number _) -> return u'
    u'@(Fraction _ _) -> return u'
    u'@(Symbol _) -> return u'

    -- trigonometric functions
    Tan' x -> do
      xSub <- trigSubstitute x
      return $ Sin' xSub / Cos' xSub

    Cot' x -> do
      xSub <- trigSubstitute x
      return $ Cos' xSub / Sin' xSub

    Sec' x -> do
      xSub <- trigSubstitute x
      return $ 1 / Cos' xSub

    Csc' x -> do
      xSub <- trigSubstitute x
      return $ 1 / Sin' xSub

    -- -- compound expressions
    Product xs  -> do
      xsSub <- mapM trigSubstitute xs
      return $ Product xsSub

    Sum xs      -> do
      xsSub <- mapM trigSubstitute xs
      return $ Sum xsSub

    Quotient n d -> do
      nSub <- trigSubstitute n
      dSub <- trigSubstitute d
      return $ nSub / dSub

    UnaryDifference x -> do
      xSub <- trigSubstitute x
      return $ negate xSub

    BinaryDifference x y -> do
      xSub <- trigSubstitute x
      ySub <- trigSubstitute y
      return $ xSub - ySub

    Power x y     -> do
      xSub <- trigSubstitute x
      ySub <- trigSubstitute y
      return $ xSub ** ySub

    Factorial x -> do
      xSub <- trigSubstitute x
      return $ Factorial xSub

    -- other functions remain unevaluated for now
    Function name args -> do
      args' <- mapM trigSubstitute args
      return $ Function name args'

