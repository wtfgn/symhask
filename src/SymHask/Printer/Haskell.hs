module SymHask.Printer.Haskell
    ( toHaskell
    ) where

import           Data.List             (intersperse)
import qualified Data.List.NonEmpty    as NE
import           Data.Text             (Text)
import           SymHask.Symbolic
import           TextShow              (showt)

-- | Convert an expression to a Haskell expression
toHaskell :: Expr a -> Text
toHaskell = \case
  Number' n -> showt n
  Symbol' s -> s

  x :-: y@(_ :+: _) -> asAddArg x <> " - " <> asArg y
  x :-: y@(_ :-: _) -> asAddArg x <> " - " <> asArg y
  UnaryDiff' x -> "-" <> asAddArg x
  BinaryDiff' x y -> asAddArg x <> " - " <> asAddArg y

  Fraction' n d ->
    let nStr = asArg (mkNumber n)
        dStr = asArg (mkNumber d)
    in nStr <> " / " <> dStr

  Quotient' n d -> asArg n <> " / " <> asArg d
  Power' x y -> asArg x <> " ^ " <> asArg y
  Factorial' x -> asArg x <> "!"

  Product' xs ->
    let factors = NE.toList xs
        factorStrs = map asMultiplyArg factors
    in  mconcat $ intersperse " * " factorStrs

  Sum' xs ->
    let terms = NE.toList xs
        termStrs = map asAddArg terms
    in  mconcat $ intersperse " + " termStrs

  Function' fname args ->
    let argStrs = map asArg $ NE.toList args
    in fname <> " " <> mconcat (intersperse " " argStrs)

-- | Show numbers and symbols as is, while surrounding everything
-- else in parentheses.
asArg :: Expr a -> Text
asArg x@(Number' n)
  | n >= 0 = toHaskell x
  | otherwise = "(" <> toHaskell x <> ")"
asArg x@(Symbol' _) = toHaskell x
asArg x = par $ toHaskell x

-- | Converts an 'Expression' to an argument appropriate for addition.
asAddArg :: Expr a -> Text
asAddArg x@(Number' _) = asArg x
asAddArg x@(Symbol' _) = asArg x
-- No operation has lower precedence than addition,
-- and addition is commutative, so no parentheses are needed.
asAddArg x             = toHaskell x

-- | Converts an 'Expression' to an argument appropriate for multiplication.
asMultiplyArg :: Expr a -> Text
asMultiplyArg x@(Number' _)       = asArg x
asMultiplyArg x@(Symbol' _)       = asArg x
asMultiplyArg x@(Sum' _)          = par $ toHaskell x
asMultiplyArg x@(UnaryDiff' _)    = par $ toHaskell x
asMultiplyArg x@(BinaryDiff' _ _) = par $ toHaskell x
-- No other operation has lower precedence than multiplication,
-- and multiplication is commutative, so no parentheses are needed.
asMultiplyArg x                   = toHaskell x

-- | Add parentheses around a string
par :: Text -> Text
par s = "(" <> s <> ")"
