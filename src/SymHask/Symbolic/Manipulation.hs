module SymHask.Symbolic.Manipulation
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

import           SymHask.Symbolic.Manipulation.Substitution




