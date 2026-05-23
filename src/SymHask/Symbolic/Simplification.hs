{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- |
-- Module: SymHask.Symbolic.Simplification
-- Description: Automatic simplification of symbolic expressions
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
--
-- This module provides support for automatic simplification of symbolic expressions.
module SymHask.Symbolic.Simplification
    ( (.**.)
    , (.*.)
    , (.+.)
    , (.-.)
    , (./.)
    ) where

import           Data.Coerce                                             (coerce)
import           SymHask.Symbolic
import           SymHask.Symbolic.Simplification.AutomaticSimplification (automaticSimplify)
import           SymHask.Symbolic.Simplification.RationalNumber          ()

-- ===========================================================================

-- * Infix Operators with Simplification

-- ===========================================================================
infixl 6 .+., .-.
infixl 7 .*., ./.
infixr 8 .**.

-- | These are just shorthands for constructing the corresponding UnsimplifiedExpr and then simplifying it.
-- Not for building large expressions due to potential performance issues with repeated simplification.
(.+.), (.-.), (.*.), (./.), (.**.) :: SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
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
  simplify = coerce automaticSimplify

instance Simplify SimplifiedExpr where
  type Simplification SimplifiedExpr = SimplifiedExpr
  simplify :: SimplifiedExpr -> EvalResult SimplifiedExpr
  simplify = pure
