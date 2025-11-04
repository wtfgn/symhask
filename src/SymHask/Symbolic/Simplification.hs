{-# LANGUAGE ViewPatterns #-}
module SymHask.Symbolic.Simplification
    ( -- Re-export core framework
      module SymHask.Symbolic
    , (.**.)
    , (.*.)
    , (.+.)
    , (.-.)
    , (./.)
    ) where

import           SymHask.Symbolic
import           SymHask.Symbolic.Simplification.AutomaticSimplification ()
import           SymHask.Symbolic.Simplification.RationalNumber          ()

infixl 6 .+., .-.
infixl 7 .*., ./.
infixr 8 .**.

(.+.), (.-.), (.*.), (./.), (.**.):: SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
(.+.) (unsimplify -> x) (unsimplify -> y) =
  simplify (x + y)

(.-.) (unsimplify -> x) (unsimplify -> y) =
  simplify (x - y)

(.*.) (unsimplify -> x) (unsimplify -> y) =
  simplify (x * y)

(./.) (unsimplify -> x) (unsimplify -> y) =
  simplify (x / y)

(.**.) (unsimplify -> b) (unsimplify -> e) =
  simplify (b ** e)

