{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# OPTIONS_GHC -Wno-orphans #-} 
{-# LANGUAGE TypeFamilies #-}

module SymHask.Symbolic.Simplification
    ( (.**.)
    , (.*.)
    , (.+.)
    , (.-.)
    , (./.)
    ) where

import           SymHask.Symbolic
import           SymHask.Symbolic.Simplification.AutomaticSimplification (automaticSimplify)
import           SymHask.Symbolic.Simplification.RationalNumber          ()
import          Data.Coerce                                          (coerce)


-- ===========================================================================
-- * Infix Operators with Simplification
-- ===========================================================================
infixl 6 .+., .-.
infixl 7 .*., ./.
infixr 8 .**.

(.+.), (.-.), (.*.), (./.), (.**.):: SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
(.+.) (unsimplify -> x) (unsimplify -> y) = simplify (x + y)
(.-.) (unsimplify -> x) (unsimplify -> y) = simplify (x - y)
(.*.) (unsimplify -> x) (unsimplify -> y) = simplify (x * y)
(./.) (unsimplify -> n) (unsimplify -> d) = simplify (n / d)
(.**.) (unsimplify -> b) (unsimplify -> e) = simplify (b ** e)


-- ===========================================================================
-- * Simplifiable Instances
-- ===========================================================================

instance Simplify UnsimplifiedExpr where
  type Simplification UnsimplifiedExpr = SimplifiedExpr
  simplify :: UnsimplifiedExpr -> EvalResult SimplifiedExpr
  simplify =  coerce automaticSimplify

instance Simplify SimplifiedExpr where
  type Simplification SimplifiedExpr = SimplifiedExpr
  simplify :: SimplifiedExpr -> EvalResult SimplifiedExpr
  simplify = pure
