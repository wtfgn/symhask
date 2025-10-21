{-# LANGUAGE ViewPatterns #-}

module SymHask.Symbolic.Manipulation
    ( module SymHask.Symbolic.Manipulation.Substitution
    ) where

import           Control.Monad                                   (foldM)
import           Data.List                                       (foldl')
import           Data.List.NonEmpty                              (NonEmpty ((:|)))
import qualified Data.List.NonEmpty                              as NE
import           Data.Text                                       (Text)
import           SymHask.Core.Expression
import           SymHask.Symbolic.Analysis
import           SymHask.Symbolic.Manipulation.Substitution
import           SymHask.Symbolic.Simplification



