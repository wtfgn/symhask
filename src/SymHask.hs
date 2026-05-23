
-- |
-- Module: SymHask
-- Description: A symbolic mathematics library in Haskell
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
--
-- SymHask is a symbolic mathematics library in Haskell
-- that provides tools for symbolic computation,
-- including simplification, differntiation, integration,
-- and polynomial manipulation.
--
-- Usually, this is the only module you need to import
-- to access all the functionality of SymHask.
-- It re-exports all the relevant modules, so you can use the library
-- without worrying about the internal structure.
-- Other modules are organized into submodules for better maintainability and clarity,
--
-- For example, to expand an expression, you can simply do:
--
-- >>> import SymHask
-- >>> let expr = ("x" + 1)**2 :: UnsimplifiedExpr
-- >>> let result = (simplify expr) >>= algebraicExpand
-- >>> result
-- Right (Sum (Number 1 :| [Product (Number 2 :| [Symbol "x"]),Power (Symbol "x") (Number 2)]))
--
-- To make it more readable, you can do:
--
-- >>> toHaskell <$> result
-- Right "1 + 2 * x + x ^ 2"
module SymHask
    ( module SymHask.Printer
    , module SymHask.Symbolic
    , module SymHask.Symbolic.Basic
    , module SymHask.Symbolic.Calculus
    , module SymHask.Symbolic.Polynomial
    , module SymHask.Symbolic.Simplification
    , module SymHask.Symbolic.Transcendental
    ) where


import           SymHask.Printer
import           SymHask.Symbolic
import           SymHask.Symbolic.Basic
import           SymHask.Symbolic.Calculus
import           SymHask.Symbolic.Polynomial
import           SymHask.Symbolic.Simplification
import           SymHask.Symbolic.Transcendental
