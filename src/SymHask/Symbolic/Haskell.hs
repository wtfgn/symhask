module SymHask.Symbolic.Haskell 
  ( toHaskell
  ) where

import Data.Text (Text)
import SymHask.Symbolic
import TextShow (showt)
import qualified Data.List.NonEmpty as NE
import Data.List (intersperse)

-- | Convert an expression to a Haskell expression
toHaskell :: Expression -> Text
toHaskell = \case
  Number n -> showt n
  Symbol s -> s

  x :-: y@(_ :+: _) -> asAddArg x <> " - " <> asArg y
  x :-: y@(_ :-: _) -> asAddArg x <> " - " <> asArg y
  UnaryDifference x -> "-" <> asAddArg x
  BinaryDifference x y -> asAddArg x <> " - " <> asAddArg y
  Fraction n d -> asArg (Number n) <> " / " <> asArg (Number d)
  Quotient n d -> asArg n <> " / " <> asArg d
  Power x y -> asArg x <> " ^ " <> asArg y
  Factorial x -> asArg x <> "!"

  Product xs ->
    let factors = NE.toList xs
        factorStrs = map asMultiplyArg factors
    in  mconcat $ intersperse " * " factorStrs

  Sum xs ->
    let terms = NE.toList xs
        termStrs = map asAddArg terms
    in  mconcat $ intersperse " + " termStrs

  Function fname args ->
    let argStrs = map asArg $ NE.toList args
    in fname <> " " <> mconcat (intersperse " " argStrs)

-- | Show numbers and symbols as is, while surrounding everything
-- else in parentheses.
asArg :: Expression -> Text
asArg x@(Number n)
  | n >= 0 = toHaskell x
  | otherwise = "(" <> toHaskell x <> ")"
asArg x@(Symbol _) = toHaskell x
asArg x = par $ toHaskell x

-- | Converts an 'Expression' to an argument appropriate for addition.
asAddArg :: Expression -> Text
asAddArg x@(Number _) = asArg x
asAddArg x@(Symbol _) = asArg x
-- No operation has lower precedence than addition,
-- and addition is commutative, so no parentheses are needed.
asAddArg x = toHaskell x

-- | Converts an 'Expression' to an argument appropriate for multiplication.
asMultiplyArg :: Expression -> Text
asMultiplyArg x@(Number _) = asArg x
asMultiplyArg x@(Symbol _) = asArg x
asMultiplyArg x@(_ :+: _) = par $ toHaskell x
asMultiplyArg x@(_ :-: _) = par $ toHaskell x
-- No other operation has lower precedence than multiplication,
-- and multiplication is commutative, so no parentheses are needed.
asMultiplyArg x = toHaskell x

-- | Add parentheses around a string
par :: Text -> Text
par s = "(" <> s <> ")"