{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}


-- |
-- Module: SymHask.Symbolic
-- Description: Core symbolic expression AST and utilities.
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
module SymHask.Symbolic
    ( -- * Representation
      Expr ()
      -- * Error Types
    , ExprError (..)
      -- * Evaluation Result Type
    , EvalResult
      -- * Type Aliases for Simplified and Unsimplified Expressions
    , SimplifiedExpr
    , UnsimplifiedExpr
      -- * Simplification Framework
    , SimplificationState (..)
    , Simplify (..)
    , unsimplify
      -- * Predicates
    , isAtomic
    , isBinaryDiff
    , isConstant
    , isFactorial
    , isFraction
    , isFunction
    , isNumber
    , isNumerical
    , isPower
    , isProduct
    , isQuotient
    , isSum
    , isSymbol
    , isUnaryDiff
      -- * Smart Constructors
    , mkBinaryDiff
    , mkFactorial
    , mkFraction
    , mkFunction
    , mkMax
    , mkNumber
    , mkPower
    , mkProduct
    , mkQuotient
    , mkSum
    , mkSymbol
    , mkUnaryDiff
    , (!)
      -- * Pattern Synonyms
      -- ** Expressions
      -- | When matching on these patterns, the underlying constructor is not exposed,
      -- so they can only be used for pattern matching, not construction.
      -- Use the smart constructors for construction instead.
    , pattern BinaryDiff'
    , pattern Factorial'
    , pattern Fraction'
    , pattern Function'
    , pattern Number'
    , pattern Power'
    , pattern Product'
    , pattern Quotient'
    , pattern Sum'
    , pattern Symbol'
    , pattern UnaryDiff'
      -- ** Common Functions and Operations
    , pattern (:**:)
    , pattern (:*:)
    , pattern (:+:)
    , pattern (:-:)
    , pattern (:/:)
    , pattern Abs'
    , pattern Acos'
    , pattern Acosh'
    , pattern Acot'
    , pattern Acoth'
    , pattern Acsc'
    , pattern Acsch'
    , pattern Asec'
    , pattern Asech'
    , pattern Asin'
    , pattern Asinh'
    , pattern Atan'
    , pattern Atanh'
    , pattern Cos'
    , pattern Cosh'
    , pattern Cot'
    , pattern Coth'
    , pattern Csc'
    , pattern Csch'
    , pattern E'
    , pattern Exp'
    , pattern I'
    , pattern Log'
    , pattern LogBase'
    , pattern Max'
    , pattern Negate'
    , pattern Pi'
    , pattern Sec'
    , pattern Sech'
    , pattern Signum'
    , pattern Sin'
    , pattern Sinh'
    , pattern Sqrt'
    , pattern Tan'
    , pattern Tanh'
    ) where

import           Control.DeepSeq    (NFData)
import           Data.Coerce        (coerce)
import           Data.Hashable      (Hashable)
import qualified Data.HashSet       as HS
import           Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import           Data.Ratio         (denominator, numerator)
import           Data.String        (IsString (..))
import           Data.Text          (Text)
import qualified Data.Text          as T
import           GHC.Generics       (Generic)
import           TextShow           (TextShow)
import           TextShow.Generic   (FromGeneric (FromGeneric))


-- ============================================================================
-- * Complete GADT for All Expression Types
-- ============================================================================
-- $setup
-- >>> import SymHask.Printer.Haskell (toHaskell)
-- Module `SymHask.Printer.Haskell' does not export `toHaskell'.

-- | Core symbolic expression type.
-- Its parameter indicates whether the expression is simplified or not.
-- Most of the operators requires the operands to be `SimplifiedExpr`,
-- because they only work correctly in the automatic simplification context.
-- Notice that it is an instance of the typeclasses `Num`, `Fractional`, and `Floating`,
-- so that you can use standard numeric syntax to construct expressions.
-- It is also an instance of `IsString`,
-- so that you can use string literals to create symbols with the @Overloadable@ pragma.
--
-- >>> 114514 :: UnsimplifiedExpr
-- Number 114514
--
-- >>> "x" :: UnsimplifiedExpr
-- Symbol "x"
--
-- >>> sin "x" + cos "x" :: UnsimplifiedExpr
-- Sum (Function "sin" (Symbol "x" :| []) :| [Function "cos" (Symbol "x" :| [])])
data Expr (a :: SimplificationState)
  = Number Integer
  | Fraction Integer Integer
  | Symbol Text
  -- Compound algebraic expressions
  | Product (NonEmpty (Expr a))
  | Sum (NonEmpty (Expr a))
  | Quotient (Expr a) (Expr a)
  | Power (Expr a) (Expr a)
  -- Advanced expressions
  | Function Text (NonEmpty (Expr a))
  | Factorial (Expr a)
  -- Differences (eliminated during simplification)
  | UnaryDiff (Expr a)
  | BinaryDiff (Expr a) (Expr a)
  -- | Structural equality only
  deriving (Eq, Generic, Hashable, NFData, Read, Show)
  deriving (TextShow)
    via FromGeneric (Expr a)

type UnsimplifiedExpr = Expr 'Unsimplified
type SimplifiedExpr = Expr 'Simplified

-- ============================================================================
-- * Error Types
-- ============================================================================

-- | Errors raised during expression evaluation and transformation.
--
-- Typical errors include `DivisionByZero` and `UnsupportedOperation`.
data ExprError
  -- | Attempted division by zero during evaluation.
  = DivisionByZero
  -- | Function applied to an argument outside its domain (e.g. log(-1)).
  | InvalidDomain Text
  -- | Operation not supported by the current implementation (e.g. `evalMax` on an empty set).
  | UnsupportedOperation Text
  -- | Generic evaluation failure with a message.
  | EvaluationFailure Text
  deriving (Eq, Show)

-- | Result type used by simplification/evaluation code.
type EvalResult a = Either ExprError a

-- ============================================================================
-- * Type Class Instances
-- ============================================================================
instance IsString (Expr a) where
  fromString :: String -> Expr a
  fromString = Symbol . T.pack

instance Num UnsimplifiedExpr where
  (+) :: UnsimplifiedExpr -> UnsimplifiedExpr -> UnsimplifiedExpr
  x + y = Sum (x :| [y])

  (*) :: UnsimplifiedExpr -> UnsimplifiedExpr -> UnsimplifiedExpr
  x * y = Product (x :| [y])

  negate :: UnsimplifiedExpr -> UnsimplifiedExpr
  negate = UnaryDiff

  abs :: UnsimplifiedExpr -> UnsimplifiedExpr
  abs = Function "abs" . NE.singleton

  signum :: UnsimplifiedExpr -> UnsimplifiedExpr
  signum = Function "signum" . NE.singleton

  fromInteger :: Integer -> UnsimplifiedExpr
  fromInteger = Number

instance Fractional UnsimplifiedExpr where
  (/) :: UnsimplifiedExpr -> UnsimplifiedExpr -> UnsimplifiedExpr
  x / y = Quotient x y

  fromRational :: Rational -> UnsimplifiedExpr
  fromRational r = Fraction (numerator r) (denominator r)

instance Floating UnsimplifiedExpr where
  pi :: UnsimplifiedExpr
  pi = Symbol "pi"

  exp :: UnsimplifiedExpr -> UnsimplifiedExpr
  exp = Function "exp" . NE.singleton

  log :: UnsimplifiedExpr -> UnsimplifiedExpr
  log = Function "log" . NE.singleton

  (**) :: UnsimplifiedExpr -> UnsimplifiedExpr -> UnsimplifiedExpr
  x ** y = Power x y

  logBase :: UnsimplifiedExpr -> UnsimplifiedExpr -> UnsimplifiedExpr
  logBase x y = Function "logBase" (x :| [y])

  sin :: UnsimplifiedExpr -> UnsimplifiedExpr
  sin = Function "sin" . NE.singleton

  cos :: UnsimplifiedExpr -> UnsimplifiedExpr
  cos = Function "cos" . NE.singleton

  asin :: UnsimplifiedExpr -> UnsimplifiedExpr
  asin = Function "asin" . NE.singleton

  acos :: UnsimplifiedExpr -> UnsimplifiedExpr
  acos = Function "acos" . NE.singleton

  atan :: UnsimplifiedExpr -> UnsimplifiedExpr
  atan = Function "atan" . NE.singleton

  sinh :: UnsimplifiedExpr -> UnsimplifiedExpr
  sinh = Function "sinh" . NE.singleton

  cosh :: UnsimplifiedExpr -> UnsimplifiedExpr
  cosh = Function "cosh" . NE.singleton

  asinh :: UnsimplifiedExpr -> UnsimplifiedExpr
  asinh = Function "asinh" . NE.singleton

  acosh :: UnsimplifiedExpr -> UnsimplifiedExpr
  acosh = Function "acosh" . NE.singleton

  atanh :: UnsimplifiedExpr -> UnsimplifiedExpr
  atanh = Function "atanh" . NE.singleton

-- ============================================================================
-- * Pattern Synonyms
-- ============================================================================
pattern Pi', E', I' :: Expr a
pattern Pi' = Symbol "pi"
pattern E' = Symbol "e"
pattern I' = Symbol "i"

pattern (:+:) :: () => Expr a -> Expr a -> Expr a
pattern x :+: y = Sum (x :| [y])
pattern (:*:) :: () => Expr a -> Expr a -> Expr a
pattern x :*: y = Product (x :| [y])
pattern (:-:) :: () => Expr a -> Expr a -> Expr a
pattern x :-: y = BinaryDiff x y
pattern (:/:) :: () => Expr a -> Expr a -> Expr a
pattern x :/: y = Quotient x y
pattern (:**:) :: () => Expr a -> Expr a -> Expr a
pattern x :**: y = Power x y
pattern LogBase' :: () => Expr a -> Expr a -> Expr a
pattern LogBase' x y = Function "logBase" (x :| [y])

pattern
  Negate', Abs', Signum', Exp', Log', Sqrt',
  Sin', Cos', Tan', Cot', Sec', Csc',
  Asin', Acos', Atan', Acot', Asec', Acsc',
  Sinh', Cosh', Tanh', Coth', Sech', Csch',
  Asinh', Acosh', Atanh', Acoth', Asech', Acsch'
  :: () => Expr a -> Expr a
pattern Negate' x = Function "negate" (x :| []) -- | `negate`
pattern Abs' x = Function "abs" (x :| []) -- | `abs`
pattern Signum' x = Function "signum" (x :| []) -- | `signum`
pattern Exp' x = Function "exp" (x :| []) -- | `exp`
pattern Log' x = Function "log" (x :| []) -- | `log`
pattern Sqrt' x = Function "sqrt" (x :| []) -- | `sqrt`
pattern Sin' x = Function "sin" (x :| []) -- | `sin`
pattern Cos' x = Function "cos" (x :| []) -- | `cos`
pattern Tan' x = Function "tan" (x :| []) -- | `tan`
pattern Cot' x = Function "cot" (x :| []) -- | `cot`
pattern Sec' x = Function "sec" (x :| []) -- | `sec`
pattern Csc' x = Function "csc" (x :| []) -- | `csc`
pattern Asin' x = Function "asin" (x :| []) -- | `asin`
pattern Acos' x = Function "acos" (x :| []) -- | `acos`
pattern Atan' x = Function "atan" (x :| []) -- | `atan`
pattern Acot' x = Function "acot" (x :| []) -- | `acot`
pattern Asec' x = Function "asec" (x :| []) -- | `asec`
pattern Acsc' x = Function "acsc" (x :| []) -- | `acsc`
pattern Sinh' x = Function "sinh" (x :| []) -- | `sinh`
pattern Cosh' x = Function "cosh" (x :| []) -- | `cosh`
pattern Tanh' x = Function "tanh" (x :| []) -- | `tanh`
pattern Coth' x = Function "coth" (x :| []) -- | `coth`
pattern Sech' x = Function "sech" (x :| []) -- | `sech`
pattern Csch' x = Function "csch" (x :| []) -- | `csch`
pattern Asinh' x = Function "asinh" (x :| []) -- | `asinh`
pattern Acosh' x = Function "acosh" (x :| []) -- | `acosh`
pattern Atanh' x = Function "atanh" (x :| []) -- | `atanh`
pattern Acoth' x = Function "acoth" (x :| []) -- | `acoth`
pattern Asech' x = Function "asech" (x :| []) -- | `asech`
pattern Acsch' x = Function "acsch" (x :| []) -- | `acsch`

-- | Only the pattern are exported, but not the underlying constructor
pattern Number' :: Integer -> Expr a
pattern Number' n <- Number n
pattern Fraction' :: Integer -> Integer -> Expr a
pattern Fraction' n d <- Fraction n d
pattern Symbol' :: Text -> Expr a
pattern Symbol' s <- Symbol s
pattern Product' :: NonEmpty (Expr a) -> Expr a
pattern Product' xs <- Product xs
pattern Sum' :: NonEmpty (Expr a) -> Expr a
pattern Sum' xs <- Sum xs
pattern Quotient' :: Expr a -> Expr a -> Expr a
pattern Quotient' x y <- Quotient x y
pattern Power' :: Expr a -> Expr a -> Expr a
pattern Power' x y <- Power x y
pattern Function' :: Text -> NonEmpty (Expr a) -> Expr a
pattern Function' name args <- Function name args
pattern Factorial' :: Expr a -> Expr a
pattern Factorial' x <- Factorial x
pattern UnaryDiff' :: Expr a -> Expr a
pattern UnaryDiff' x <- UnaryDiff x
pattern BinaryDiff' :: Expr a -> Expr a -> Expr a
pattern BinaryDiff' x y <- BinaryDiff x y

pattern Max' :: HS.HashSet SimplifiedExpr -> SimplifiedExpr
pattern Max' exprSet <- Function' "max" (NE.toList -> (HS.fromList -> exprSet))

{-# COMPLETE
  Number', Fraction', Symbol',
  Product', Sum', Quotient', Power',
  Function', Factorial',
  UnaryDiff', BinaryDiff'
  #-}
-- ============================================================================
-- * Smart Constructors
-- ============================================================================

mkNumber :: Integer -> Expr a
mkNumber = Number

mkFraction :: Integer -> Integer -> UnsimplifiedExpr
mkFraction = Fraction

mkSymbol :: Text -> Expr a
mkSymbol = Symbol

mkProduct :: NonEmpty (Expr a) -> UnsimplifiedExpr
mkProduct = coerce Product

mkSum :: NonEmpty (Expr a) -> UnsimplifiedExpr
mkSum = coerce Sum

mkQuotient :: Expr a -> Expr a' -> UnsimplifiedExpr
mkQuotient = coerce Quotient

mkPower :: Expr a -> Expr a' -> UnsimplifiedExpr
mkPower = coerce Power

mkFunction :: Text -> NonEmpty (Expr a) -> Expr a
mkFunction = Function

mkFactorial :: Expr a -> UnsimplifiedExpr
mkFactorial = coerce Factorial

-- | (!) operator for factorial
(!) :: Expr a -> UnsimplifiedExpr
(!) = mkFactorial

mkUnaryDiff :: Expr a -> UnsimplifiedExpr
mkUnaryDiff = coerce UnaryDiff

mkBinaryDiff :: Expr a -> Expr a' -> UnsimplifiedExpr
mkBinaryDiff =  coerce BinaryDiff

mkMax :: HS.HashSet SimplifiedExpr -> SimplifiedExpr
mkMax exprSet = mkFunction "max" (NE.fromList (HS.toList exprSet))

-- ============================================================================
-- * Helper Functions
-- ============================================================================

-- | Check if expression is a constant (`Number` or `Fraction`)
isConstant :: Expr a -> Bool
isConstant (Number' _)     = True
isConstant (Fraction' _ _) = True
isConstant _               = False

-- | Check if expression is atomic (`Number`, `Fraction`, or `Symbol`)
isAtomic :: Expr a -> Bool
isAtomic (Number' _)     = True
isAtomic (Fraction' _ _) = True
isAtomic (Symbol' _)     = True
isAtomic _               = False

-- | Check if expression is a `Number`
isNumber :: Expr a -> Bool
isNumber (Number' _) = True
isNumber _           = False

-- | Check if expression is a `Fraction`
isFraction :: Expr a -> Bool
isFraction (Fraction' _ _) = True
isFraction _               = False

-- | Check if expression is a `Symbol`
isSymbol :: Expr a -> Bool
isSymbol (Symbol' _) = True
isSymbol _           = False

-- | Check if expression is a `Function`
isFunction :: Expr a -> Bool
isFunction (Function' _ _) = True
isFunction _               = False

-- | Check if expression is a `Product`
isProduct :: Expr a -> Bool
isProduct (Product' _) = True
isProduct _            = False

-- | Check if expression is a `Sum`
isSum :: Expr a -> Bool
isSum (Sum' _) = True
isSum _        = False

-- | Check if expression is a `Quotient`
isQuotient :: Expr a -> Bool
isQuotient (Quotient' _ _) = True
isQuotient _               = False

-- | Check if expression is a `Power`
isPower :: Expr a -> Bool
isPower (Power' _ _) = True
isPower _            = False

-- | Check if expression is a `Factorial`
isFactorial :: Expr a -> Bool
isFactorial (Factorial' _) = True
isFactorial _              = False

-- | Check if expression is a `UnaryDiff`
isUnaryDiff :: Expr a -> Bool
isUnaryDiff (UnaryDiff' _) = True
isUnaryDiff _              = False

-- | Check if expression is a `BinaryDiff`
isBinaryDiff :: Expr a -> Bool
isBinaryDiff (BinaryDiff' _ _) = True
isBinaryDiff _                 = False

-- | Check if expression is numerical (i.e. contains only numbers, fractions, pi, e, and i)
isNumerical :: SimplifiedExpr -> Bool
isNumerical = \case
  Number' _     -> True
  Fraction' _ _ -> True
  Pi'         -> True
  E'         -> True
  Symbol' _     -> False
  Quotient' n d  -> isNumerical n && isNumerical d
  UnaryDiff' x   -> isNumerical x
  BinaryDiff' x y -> isNumerical x && isNumerical y
  Product' factors    -> all isNumerical factors
  Sum' terms        -> all isNumerical terms
  Power' b e -> isNumerical b && isNumerical e
  Factorial' expr  -> isNumerical expr
  Function' _ args -> all isNumerical args

-- ============================================================================
-- * Simplification Framework
-- ============================================================================

data SimplificationState
  = Simplified
  | Unsimplified

class Simplify expr where
  type Simplification expr
  -- | Simplify an expression into its simplified representation.
  -- Implementations may fail with an `ExprError`.
  simplify :: expr -> EvalResult (Simplification expr)

-- | Convert a simplified expression back to its unsimplified form.
-- This is useful for constructing new expressions from simplified subexpressions.
unsimplify :: Expr a -> UnsimplifiedExpr
unsimplify = coerce

-- instance Simplify UnsimplifiedExpr where
--   type Simplification UnsimplifiedExpr = SimplifiedExpr
--   simplify :: UnsimplifiedExpr -> EvalResult SimplifiedExpr
--   simplify expr = Right (unsafeCoerce expr) -- Placeholder implementation
