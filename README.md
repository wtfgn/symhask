# symhask

SymHask is a small computer algebra system in Haskell. It provides symbolic expression building, simplification, calculus, polynomial manipulation, transcendental functions, and pretty-printing.

It also includes a simple REPL example to demonstrate the library in action. That REPL is only an example program, not part of the core library API.

## Installation

To use SymHask locally, clone the repository and build it with Stack:

```bash
git clone https://github.com/wtfgn/symhask.git
cd symhask
stack build
stack install
```

After that, you can import `SymHask` from GHCi or from your own Haskell files. If you prefer Cabal, the same workflow can be done with `cabal build` and `cabal install`.

For Stack-based projects, add SymHask as a dependency in the appropriate build target and, if needed, list it under `extra-deps` in `stack.yaml`.

```yaml
# stack.yaml
extra-deps:
  - symhask
```

## Quick Start

In [GHCi]:

```shell
$ stack ghci --no-load
```

Then, load the `SymHask` module.

```haskell
>>> :load SymHask
>>> let expr = "x"**2 + 2*"x" + 1 :: UnsimplifiedExpr
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

[GHCi]: https://downloads.haskell.org/ghc/latest/docs/users_guide/ghci.html

## Module Layout

- `SymHask.Printer` for output formatting.
- `SymHask.Symbolic` for the core symbolic types.
- `SymHask.Symbolic.Basic` for basic symbolic operations.
- `SymHask.Calculus` for differentiation and integration.
- `SymHask.Polynomial` for polynomial tools.
- `SymHask.Simplification` for simplification routines.
- `SymHask.Transcendental` for transcendental functions.

## License

BSD-3-Clause
