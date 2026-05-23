# symhask

SymHask is a small computer algebra system in Haskell. It provides symbolic expression building, simplification, calculus, polynomial manipulation, transcendental functions, and pretty-printing.

It also includes a simple REPL example to demonstrate the library in action. That REPL is only an example program, not part of the core library API.

## Quick Start

In GHCi:

```haskell
:load SymHask
import SymHask
```

In a Haskell file:

```haskell
import SymHask
```

`SymHask` re-exports the main API, so this single import is usually enough.

## What It Can Do

- Build symbolic expressions with numbers, symbols, and standard operators.
- Simplify expressions.
- Differentiate and integrate symbolically.
- Expand and manipulate polynomials.
- Work with transcendental functions.
- Print expressions in Haskell-style or LaTeX-style form.
- Perform substitution and other basic symbolic operations.

## Examples

The module Haddocks contain runnable examples and API notes. A few quick examples:

```haskell
>>> let expr1 = "x"**2 + "y" :: UnsimplifiedExpr
>>> let diffVar = mkDiffVar "x"
>>> let res = do { expr' <- simplify expr1; dv <- diffVar; diff dv expr' }
>>> toHaskell <$> res
Right "2 * x"
>>>
>>> let expr2 = ("x" + 2) * ("x" + 3) * ("x" + 4):: UnsimplifiedExpr
>>> fmap toHaskell $ simplify expr2 >>= algebraicExpand
Right "24 + 26 * x + 9 * x ^ 2 + x ^ 3"
>>>
>>> let expr3 = ("x" + 1)**(5/2):: UnsimplifiedExpr
>>> fmap toHaskell $ simplify expr3 >>= algebraicExpand
Right "(1 + x) ^ (1 / 2) + 2 * x * (1 + x) ^ (1 / 2) + x ^ 2 * (1 + x) ^ (1 / 2)"
```

For more examples, see the Haddock comments in `src/SymHask.hs` and the submodules under `src/SymHask/`.

## Module Layout

- `SymHask.Printer` for output formatting.
- `SymHask.Symbolic` for the core symbolic types.
- `SymHask.Symbolic.Basic` for basic symbolic operations.
- `SymHask.Symbolic.Calculus` for differentiation and integration.
- `SymHask.Symbolic.Polynomial` for polynomial tools.
- `SymHask.Symbolic.Simplification` for simplification routines.
- `SymHask.Symbolic.Transcendental` for transcendental functions.

## License

BSD-3-Clause
