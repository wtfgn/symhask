-- |
-- Module: SymHask.Printer.LaTeX
-- Description: Convert symbolic expressions to LaTeX text
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
--
-- Support for converting symbolic representations of mathematical expressions
-- into equivalent LaTeX text.
module SymHask.Printer.LaTeX
    ( printLaTeX
    , toLaTeX
    , toLaTeXString
    ) where

import           Data.List          (intersperse)
import qualified Data.List.NonEmpty as NE
import           Data.Text          (Text)
import qualified Data.Text          as T
import qualified Data.Text.IO       as TIO
import           SymHask.Symbolic
import           TextShow           (showt)

-- | Converts an 'Expr' into an equivalent LaTeX expression.
--
-- >>> toLaTeX $ (exp 5 :: UnsimplifiedExpr)
-- WAS WAS "e^{5}"
-- WAS NOW "e^{5}"
-- NOW "e^{5}"
--
-- Symbols are included without quotation.
--
-- >>> toLaTeX $ (exp "x" :: UnsimplifiedExpr)
-- >>> toLaTeX $ (("x" + 4 * sin "y") :: UnsimplifiedExpr)
--
-- Since the text for symbols are included as is, we can also include LaTeX symbols:
--
-- >>> toLaTeX $ (exp "\\delta_0" :: UnsimplifiedExpr)
--
-- >>> putStrLn . toLaTeX $ ((sin "x" + cos pi) :: UnsimplifiedExpr)
toLaTeX :: Expr a -> Text
toLaTeX = \case
    Number' n -> showt n
    Fraction' n d -> "\\frac" <> brace (showt n) <> brace (showt d)
    Symbol' "pi" -> "\\pi"
    Symbol' s -> s
    UnaryDiff' x -> "-" <> asArg x
    BinaryDiff' x y -> asAddInitialArg x <> " - " <> asAddTrailingArg y
    Quotient' x y -> "\\frac" <> brace (toLaTeX x) <> brace (toLaTeX y)
    Power' x y -> asArg x <> "^" <> brace (toLaTeX y)
    Factorial' x -> asArg x <> "!"
    Product' xs -> mconcat $ intersperse " " (map asMultiplyArg $ NE.toList xs)
    Sum' xs -> mconcat $ intersperse " + " (map asAddArg $ NE.toList xs)
    Negate' x -> "-" <> asArg x
    Abs' x -> "\\left\\lvert " <> toLaTeX x <> " \\right\\rvert"
    Signum' x -> "\\mathrm{signum}" <> par (toLaTeX x)
    Exp' x -> "e^" <> brace (toLaTeX x)
    Log' x -> "\\log " <> asNamedFunctionArg x
    Sqrt' x -> "\\sqrt" <> brace (toLaTeX x)
    Sin' x -> "\\sin " <> asNamedFunctionArg x
    Cos' x -> "\\cos " <> asNamedFunctionArg x
    Tan' x -> "\\tan " <> asNamedFunctionArg x
    Cot' x -> "\\cot " <> asNamedFunctionArg x
    Sec' x -> "\\sec " <> asNamedFunctionArg x
    Csc' x -> "\\csc " <> asNamedFunctionArg x
    Asin' x -> "\\sin^{-1} " <> asNamedFunctionArg x
    Acos' x -> "\\cos^{-1} " <> asNamedFunctionArg x
    Atan' x -> "\\tan^{-1} " <> asNamedFunctionArg x
    Acot' x -> "\\cot^{-1} " <> asNamedFunctionArg x
    Asec' x -> "\\sec^{-1} " <> asNamedFunctionArg x
    Acsc' x -> "\\csc^{-1} " <> asNamedFunctionArg x
    Sinh' x -> "\\sinh " <> asNamedFunctionArg x
    Cosh' x -> "\\cosh " <> asNamedFunctionArg x
    Tanh' x -> "\\tanh " <> asNamedFunctionArg x
    Coth' x -> "\\coth " <> asNamedFunctionArg x
    Sech' x -> "\\sech " <> asNamedFunctionArg x
    Csch' x -> "\\csch " <> asNamedFunctionArg x
    Asinh' x -> "\\sinh^{-1} " <> asNamedFunctionArg x
    Acosh' x -> "\\cosh^{-1} " <> asNamedFunctionArg x
    Atanh' x -> "\\tanh^{-1} " <> asNamedFunctionArg x
    Acoth' x -> "\\coth^{-1} " <> asNamedFunctionArg x
    Asech' x -> "\\sech^{-1} " <> asNamedFunctionArg x
    Acsch' x -> "\\csch^{-1} " <> asNamedFunctionArg x
    LogBase' x y -> "\\log_" <> brace (toLaTeX x) <> asNamedFunctionArg y
    Function' "max" args -> "\\max " <> par (mconcat $ intersperse ", " (map toLaTeX $ NE.toList args))
    Function' fname args -> fname <> " " <> mconcat (intersperse " " (map asArg $ NE.toList args))

asArg :: Expr a -> Text
asArg e@(Number' n)
    | n >= 0 = toLaTeX e
    | otherwise = par $ toLaTeX e
asArg e@(Fraction' _ _) = par $ toLaTeX e
asArg e@(Symbol' _) = toLaTeX e
asArg e@(UnaryDiff' _) = par $ toLaTeX e
asArg e@(BinaryDiff' _ _) = par $ toLaTeX e
asArg e@(Quotient' _ _) = toLaTeX e
asArg e@(Power' _ _) = par $ toLaTeX e
asArg e@(Function' _ _) = toLaTeX e
asArg e@(Factorial' _) = toLaTeX e
asArg e = par $ toLaTeX e

asAddArg :: Expr a -> Text
asAddArg e@(Number' _)       = asArg e
asAddArg e@(Fraction' _ _)   = asArg e
asAddArg e@(Symbol' _)       = asArg e
asAddArg e@(UnaryDiff' _)    = asArg e
asAddArg e@(BinaryDiff' _ _) = asArg e
asAddArg e                   = toLaTeX e

asAddInitialArg :: Expr a -> Text
asAddInitialArg e@(Number' _) = toLaTeX e
asAddInitialArg e@(Fraction' _ _) = toLaTeX e
asAddInitialArg e@(Symbol' _) = toLaTeX e
asAddInitialArg e@(UnaryDiff' _) = toLaTeX e
asAddInitialArg (BinaryDiff' x y) = asAddInitialArg x <> " - " <> asAddTrailingArg y
asAddInitialArg e = asAddArg e

asAddTrailingArg :: Expr a -> Text
asAddTrailingArg e@(Number' _)     = asArg e
asAddTrailingArg e@(Fraction' _ _) = asArg e
asAddTrailingArg e@(Symbol' _)     = asArg e
asAddTrailingArg e@(UnaryDiff' _)  = asArg e
asAddTrailingArg e                 = toLaTeX e

asMultiplyArg :: Expr a -> Text
asMultiplyArg e@(Number' _)       = asArg e
asMultiplyArg e@(Fraction' _ _)   = asArg e
asMultiplyArg e@(Symbol' _)       = asArg e
asMultiplyArg e@(UnaryDiff' _)    = asArg e
asMultiplyArg e@(Quotient' _ _)   = par $ toLaTeX e
asMultiplyArg e@(Power' _ _)      = toLaTeX e
asMultiplyArg e@(Sum' _)          = asArg e
asMultiplyArg e@(BinaryDiff' _ _) = asArg e
asMultiplyArg e@(Function' _ _)   = toLaTeX e
asMultiplyArg e@(Factorial' _)    = toLaTeX e
asMultiplyArg e                   = par $ toLaTeX e

-- For arguments to named functions such as "sin" which do not always delimit their arguments.
-- E.g., it is preferred that "1 + sin x" be "1 + sin x" and not "1 + (sin x)",
-- but we want "cos (sin x)" to be "cos (sin x)" and not "cos sin x".
asNamedFunctionArg :: Expr a -> Text
asNamedFunctionArg e@(Exp' _)          = asArg e
asNamedFunctionArg e@(Abs' _)          = asArg e
asNamedFunctionArg e@(Sqrt' _)         = asArg e
asNamedFunctionArg e@(Function' _ _)   = par $ toLaTeX e
asNamedFunctionArg e@(Quotient' _ _)   = par $ toLaTeX e
asNamedFunctionArg e@(Power' _ _)      = par $ toLaTeX e
asNamedFunctionArg e@(Sum' _)          = par $ toLaTeX e
asNamedFunctionArg e@(BinaryDiff' _ _) = par $ toLaTeX e
asNamedFunctionArg e@(LogBase' _ _)    = par $ toLaTeX e
asNamedFunctionArg e                   = asArg e

par :: Text -> Text
par s = "\\left(" <> s <> "\\right)"

brace :: Text -> Text
brace s = "{" <> s <> "}"

-- | Convert LaTeX `Text` to a plain `String` suitable for copying.
toLaTeXString :: Expr a -> String
toLaTeXString = T.unpack . toLaTeX

-- | Print LaTeX unescaped to stdout (useful in GHCi for copying).
printLaTeX :: Expr a -> IO ()
printLaTeX = TIO.putStrLn . toLaTeX
