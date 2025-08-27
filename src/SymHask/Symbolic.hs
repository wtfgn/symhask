{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE InstanceSigs    #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PatternSynonyms #-}

module SymHask.Symbolic
    ( -- * Core Data Types
      Expression (..)
    , ExpressionResult (..)
    , Operands
      -- * Smart Constructors
    , mkBinaryDifference
    , mkFactorial
    , mkFraction
    , mkFunction
    , mkNumber
    , mkPower
    , mkProduct
    , mkQuotient
    , mkSum
    , mkSymbol
    , mkUnaryDifference
      -- * Predicates
    , isBinaryDifference
    , isConstant
    , isFactorial
    , isFraction
    , isFunction
    , isNumber
    , isPower
    , isProduct
    , isQuotient
    , isSum
    , isSymbol
    , isUnaryDifference
      -- * Helper Functions
    , getBinaryFunction
    , getConst
    , getOperands
    , getPowerBase
    , getPowerExponent
    , getTerm
    , getUnaryFunction
    , toEither
    , toMaybe
      -- * Pattern Synonyms
    , isAtomic
    , pattern (:**:)
    , pattern (:*:)
    , pattern (:+:)
    , pattern (:-:)
    , pattern (:/:)
    , pattern Abs'
    , pattern Acos'
    , pattern Acosh'
    , pattern Asin'
    , pattern Asinh'
    , pattern Atan'
    , pattern Atanh'
    , pattern Cos'
    , pattern Cosh'
    , pattern Exp'
    , pattern Log'
    , pattern LogBase'
    , pattern Negate'
    , pattern Signum'
    , pattern Sin'
    , pattern Sinh'
    , pattern Sqrt'
    , pattern Tan'
    , pattern Tanh'
    ) where

import           Control.DeepSeq    (NFData)
import qualified Data.List.NonEmpty as NE
import           Data.Ratio         (denominator, numerator)
import           Data.String        (IsString, fromString)
import           Data.Text          (Text)
import           GHC.Generics       (Generic)
import           Prelude            hiding ((^))
import           TextShow           (TextShow)
import           TextShow.Generic   (FromGeneric (..))

-- ============================================================================
-- * Core Data Types
-- ============================================================================

type Operands = NE.NonEmpty Expression

-- | Unified symbolic expression type
-- This represents all kinds of mathematical expressions in the CAS
data Expression
  = Number Integer -- Numbers (integers)
  | Fraction Integer Integer -- Rational numbers (n/d)
  | Symbol Text -- Variables and constants
  | Product Operands -- Multiplication: a * b * c * ...
  | Sum Operands -- Addition: a + b + c + ...
  | Quotient Expression Expression -- Division: a / b
  | UnaryDifference Expression -- Unary negation: -a
  | BinaryDifference Expression Expression -- Subtraction: a - b
  | Power Expression Expression -- Exponentiation: a ^ b
  | Factorial Expression -- Factorial: n!
  | Function Text Operands -- Function application: f(x, y, ...)
  deriving (Eq, Generic, NFData, Read, Show)
  deriving (TextShow)
    via FromGeneric Expression

-- | Result type for expression operations
data ExpressionResult a
  = ExpressionSuccess a -- Successful result with an expression
  | ExpressionUndefined Text -- Mathematical undefined case
  | ExpressionError Text -- Programming/computation error
  deriving (Eq, Functor, Show)

-- ============================================================================
-- * Smart Constructors
-- ============================================================================

-- | Create a number expression
mkNumber :: Integer -> Expression
mkNumber = Number

-- | Create a fraction expression
mkFraction :: Integer -> Integer -> Expression
mkFraction = Fraction

-- | Create a symbol expression
mkSymbol :: Text -> Expression
mkSymbol = Symbol

-- | Create a sum expression
mkSum :: [Expression] -> Expression
mkSum = Sum . NE.fromList

-- | Create a product expression
mkProduct :: [Expression] -> Expression
mkProduct = Product . NE.fromList

-- | Create a unary difference expression
mkUnaryDifference :: Expression -> Expression
mkUnaryDifference = UnaryDifference

-- | Create a binary difference expression
mkBinaryDifference :: Expression -> Expression -> Expression
mkBinaryDifference = BinaryDifference

-- | Create a quotient expression
mkQuotient :: Expression -> Expression -> Expression
mkQuotient = Quotient

-- | Create a power expression
mkPower :: Expression -> Expression -> Expression
mkPower = Power

-- | Create a factorial expression
mkFactorial :: Expression -> Expression
mkFactorial = Factorial

-- | Create a function expression
mkFunction :: Text -> [Expression] -> Expression
mkFunction f args = Function f (NE.fromList args)

-- ============================================================================
-- * Predicates
-- ============================================================================

-- | Check if expression is a number
isNumber :: Expression -> Bool
isNumber (Number _) = True
isNumber _          = False

-- | Check if expression is a fraction
isFraction :: Expression -> Bool
isFraction (Fraction _ _) = True
isFraction _              = False

-- | Check if expression is a symbol
isSymbol :: Expression -> Bool
isSymbol (Symbol _) = True
isSymbol _          = False

-- | Check if expression is a product
isProduct :: Expression -> Bool
isProduct (Product _) = True
isProduct _           = False

-- | Check if expression is a sum
isSum :: Expression -> Bool
isSum (Sum _) = True
isSum _       = False

-- | Check if expression is a quotient
isQuotient :: Expression -> Bool
isQuotient (Quotient _ _) = True
isQuotient _              = False

-- | Check if expression is a unary difference
isUnaryDifference :: Expression -> Bool
isUnaryDifference (UnaryDifference _) = True
isUnaryDifference _                   = False

-- | Check if expression is a binary difference
isBinaryDifference :: Expression -> Bool
isBinaryDifference (BinaryDifference _ _) = True
isBinaryDifference _                      = False

-- | Check if expression is a power
isPower :: Expression -> Bool
isPower (Power _ _) = True
isPower _           = False

-- | Check if expression is a factorial
isFactorial :: Expression -> Bool
isFactorial (Factorial _) = True
isFactorial _             = False

-- | Check if expression is a function
isFunction :: Expression -> Bool
isFunction (Function _ _) = True
isFunction _              = False

-- | Check if expression is a constant (number or fraction)
isConstant :: Expression -> Bool
isConstant (Number _)     = True
isConstant (Fraction _ _) = True
isConstant _              = False

-- Check if expression is atomic (a constant, symbol, or number)
isAtomic :: Expression -> Bool
isAtomic (Number _)     = True
isAtomic (Fraction _ _) = True
isAtomic (Symbol _)     = True
isAtomic _              = False

-- ============================================================================
-- * Type Class Instances
-- ============================================================================

instance IsString Expression where
  fromString :: String -> Expression
  fromString = mkSymbol . fromString

-- | Arithmetic operations create simplified expressions
instance Num Expression where
  (+) :: Expression -> Expression -> Expression
  x + y = mkSum [x, y]

  (*) :: Expression -> Expression -> Expression
  x * y = mkProduct [x, y]

  (-) :: Expression -> Expression -> Expression
  x - y = mkBinaryDifference x y

  negate :: Expression -> Expression
  negate = mkUnaryDifference

  abs :: Expression -> Expression
  abs x = mkFunction "abs" [x]

  signum :: Expression -> Expression
  signum x = mkFunction "signum" [x]

  fromInteger :: Integer -> Expression
  fromInteger = mkNumber

instance Fractional Expression where
  (/) :: Expression -> Expression -> Expression
  x / y = mkQuotient x y

  fromRational :: Rational -> Expression
  fromRational r = mkFraction n d
    where
      n = numerator r
      d = denominator r

instance Floating Expression where
  pi :: Expression
  pi = mkSymbol "pi"

  exp :: Expression -> Expression
  exp x = mkFunction "exp" [x]

  log :: Expression -> Expression
  log x = mkFunction "log" [x]

  sqrt :: Expression -> Expression
  sqrt x = mkFunction "sqrt" [x]

  (**) :: Expression -> Expression -> Expression
  x ** y = mkPower x y

  logBase :: Expression -> Expression -> Expression
  logBase b x = mkFunction "logBase" [b, x]

  sin :: Expression -> Expression
  sin x = mkFunction "sin" [x]

  cos :: Expression -> Expression
  cos x = mkFunction "cos" [x]

  tan :: Expression -> Expression
  tan x = mkFunction "tan" [x]

  asin :: Expression -> Expression
  asin x = mkFunction "asin" [x]

  acos :: Expression -> Expression
  acos x = mkFunction "acos" [x]

  atan :: Expression -> Expression
  atan x = mkFunction "atan" [x]

  sinh :: Expression -> Expression
  sinh x = mkFunction "sinh" [x]

  cosh :: Expression -> Expression
  cosh x = mkFunction "cosh" [x]

  tanh :: Expression -> Expression
  tanh x = mkFunction "tanh" [x]

  asinh :: Expression -> Expression
  asinh x = mkFunction "asinh" [x]

  acosh :: Expression -> Expression
  acosh x = mkFunction "acosh" [x]

  atanh :: Expression -> Expression
  atanh x = mkFunction "atanh" [x]

-- ============================================================================
-- * Result Type Instances
-- ============================================================================

instance Applicative ExpressionResult where
  pure = ExpressionSuccess
  (ExpressionSuccess f) <*> (ExpressionSuccess x) = ExpressionSuccess (f x)
  (ExpressionUndefined msg) <*> _                 = ExpressionUndefined msg
  (ExpressionError msg) <*> _                     = ExpressionError msg
  _ <*> (ExpressionUndefined msg)                 = ExpressionUndefined msg
  _ <*> (ExpressionError msg)                     = ExpressionError msg

instance Monad ExpressionResult where
  return = pure
  (ExpressionSuccess x) >>= f     = f x
  (ExpressionUndefined msg) >>= _ = ExpressionUndefined msg
  (ExpressionError msg) >>= _     = ExpressionError msg

-- ============================================================================
-- * Pattern Synonyms
-- ============================================================================
pattern (:+:), (:*:), (:-:), (:/:), (:**:), LogBase' :: Expression -> Expression -> Expression
pattern x :+: y = Sum [x, y]
pattern x :*: y = Product [x, y]
pattern x :-: y = BinaryDifference x y
pattern x :/: y = Quotient x y
pattern x :**: y = Power x y
pattern LogBase' x y = Function "logBase" [x, y]

pattern Negate', Abs', Signum', Exp', Log', Sqrt', Sin', Cos', Tan', Asin', Acos', Atan', Sinh', Cosh', Tanh', Asinh', Acosh', Atanh' :: Expression -> Expression
pattern Negate' x = Function "negate" [x]
pattern Abs' x = Function "abs" [x]
pattern Signum' x = Function "signum" [x]
pattern Exp' x = Function "exp" [x]
pattern Log' x = Function "log" [x]
pattern Sqrt' x = Function "sqrt" [x]
pattern Sin' x = Function "sin" [x]
pattern Cos' x = Function "cos" [x]
pattern Tan' x = Function "tan" [x]
pattern Asin' x = Function "asin" [x]
pattern Acos' x = Function "acos" [x]
pattern Atan' x = Function "atan" [x]
pattern Sinh' x = Function "sinh" [x]
pattern Cosh' x = Function "cosh" [x]
pattern Tanh' x = Function "tanh" [x]
pattern Asinh' x = Function "asinh" [x]
pattern Acosh' x = Function "acosh" [x]
pattern Atanh' x = Function "atanh" [x]
-- ============================================================================
-- * Helper Functions
-- ============================================================================
getPowerBase :: Expression -> ExpressionResult Expression
getPowerBase = \case
  u@(Symbol _) -> return u
  u@(Product _) -> return u
  u@(Sum _) -> return u
  u@(Factorial _) -> return u
  u@(Function _ _) -> return u

  (Power b _) -> return b

  Number _ -> ExpressionUndefined "Power base cannot be a number"
  Fraction _ _ -> ExpressionUndefined "Power base cannot be a fraction"

  _ -> ExpressionError
    "Unsupported expression type for power base extraction, only \
    \a symbol, product, sum, factorial or function is expected."

getPowerExponent :: Expression -> ExpressionResult Expression
getPowerExponent = \case
  (Symbol _) -> return $ mkNumber 1
  (Product _) -> return $ mkNumber 1
  (Sum _) -> return $ mkNumber 1
  (Factorial _) -> return $ mkNumber 1
  (Function _ _) -> return $ mkNumber 1

  (Power _ e) -> return e

  (Number _) -> ExpressionUndefined "Power exponent cannot be a number"
  (Fraction _ _) -> ExpressionUndefined "Power exponent cannot be a fraction"

  _ -> ExpressionError
    "Unsupported expression type for power exponent extraction, only \
    \a symbol, product, sum, factorial or function is expected."

getTerm :: Expression -> ExpressionResult Expression
getTerm = \case
  u@(Symbol _) -> return $ mkProduct [u]
  u@(Sum _) -> return $ mkProduct [u]
  u@(Power _ _) -> return $ mkProduct [u]
  u@(Factorial _) -> return $ mkProduct [u]
  u@(Function _ _) -> return $ mkProduct [u]
  u@(Product (x NE.:| xs)) -> return $ if isConstant x then mkProduct xs else u

  Number _ -> ExpressionUndefined "Cannot extract term from a number"
  Fraction _ _ -> ExpressionUndefined "Cannot extract term from a fraction"

  _ -> ExpressionError
    "Unsupported expression type for term extraction, only \
    \a number, fraction, symbol, product, sum, difference, quotient, \
    \power, factorial or function is expected."

getConst :: Expression -> ExpressionResult Expression
getConst = \case
  Symbol _ -> return $ mkNumber 1
  Sum _ -> return $ mkNumber 1
  Power _ _ -> return $ mkNumber 1
  Factorial _ -> return $ mkNumber 1
  Function _ _ -> return $ mkNumber 1
  Product (x NE.:| _) -> return $ if isConstant x then x else mkNumber 1

  Number _ -> ExpressionUndefined "Cannot extract constant from a number"
  Fraction _ _ -> ExpressionUndefined "Cannot extract constant from a fraction"

  _ -> ExpressionError
    "Unsupported expression type for constant extraction, only \
    \a number, fraction, symbol, product, sum, difference, quotient, \
    \power, factorial or function is expected."

getUnaryFunction :: (Floating a) => Expression -> Maybe (a -> a)
getUnaryFunction = \case
  Negate' _ -> Just negate
  Abs' _   -> Just abs
  Signum' _ -> Just signum
  Exp' _    -> Just exp
  Log' _    -> Just log
  Sqrt' _   -> Just sqrt
  Sin' _    -> Just sin
  Cos' _    -> Just cos
  Tan' _    -> Just tan
  Asin' _   -> Just asin
  Acos' _   -> Just acos
  Atan' _   -> Just atan
  Sinh' _   -> Just sinh
  Cosh' _   -> Just cosh
  Tanh' _   -> Just tanh
  Asinh' _  -> Just asinh
  Acosh' _  -> Just acosh
  Atanh' _  -> Just atanh
  _         -> Nothing

getBinaryFunction :: (Floating a) => Expression -> Maybe (a -> a -> a)
getBinaryFunction = \case
  _ :+: _ -> Just (+)
  _ :-: _ -> Just (-)
  _ :*: _ -> Just (*)
  _ :/: _ -> Just (/)
  _ :**: _ -> Just (**)
  _       -> Nothing

toMaybe :: ExpressionResult a -> Maybe a
toMaybe = \case
  ExpressionSuccess x -> Just x
  ExpressionError _   -> Nothing
  ExpressionUndefined _ -> Nothing

toEither :: ExpressionResult a -> Either Text a
toEither = \case
  ExpressionSuccess x -> Right x
  ExpressionError msg -> Left msg
  ExpressionUndefined msg -> Left msg

getOperands :: Expression -> Operands
getOperands (Product xs)           = xs
getOperands (Sum xs)               = xs
getOperands (Quotient n d)         = [n, d]
getOperands (UnaryDifference x)    = [x]
getOperands (BinaryDifference x y) = [x, y]
getOperands (Power x y)            = [x, y]
getOperands (Factorial x)          = [x]
getOperands (Function _ args)      = args
getOperands _                      = []

-- ============================================================================
-- * Canonical Ordering Instance
-- ============================================================================

-- | Canonical ordering instance for Expression
-- This provides a total order suitable for general use
instance Ord Expression where
  compare :: Expression -> Expression -> Ordering
  -- Compare constants
  compare (Number n1) (Number n2) = compare n1 n2
  compare (Fraction n1 d1) (Fraction n2 d2) = compare (n1 * d2) (n2 * d1)
  compare (Number x) (Fraction n d) = compare (x * d) n
  compare (Fraction n d) (Number x) = compare n (x * d)

  -- Compare symbols (lexicographically)
  compare (Symbol s1) (Symbol s2) = compare s1 s2

  -- Compare products and sums by their operands
  compare (Product xs1) (Product xs2) =
    compareOperandList (NE.reverse xs1) (NE.reverse xs2)
  compare (Sum xs1) (Sum xs2) =
    compareOperandList (NE.reverse xs1) (NE.reverse xs2)

  -- Compare powers by base and exponent
  compare u@(Power _ _) v@(Power _ _) =
    case do
      b1 <- getPowerBase u
      b2 <- getPowerBase v
      e1 <- getPowerExponent u
      e2 <- getPowerExponent v
      case compare b1 b2 of
        EQ    -> return $ compare e1 e2
        other -> return other
    of
      ExpressionSuccess ord -> ord
      _                     -> EQ -- Fallback if extraction fails

  -- Compare factorials
  compare (Factorial x) (Factorial y) = compare x y

  -- Compare functions by name and arguments
  compare (Function f1 args1) (Function f2 args2) =
    case compare f1 f2 of
      EQ    -> compareOperandList args1 args2
      other -> other

  -- Compare when one is an integer or fraction and the other is any other type
  -- This ensures constant must be the first operand
  compare (Number _) _ = LT
  compare (Fraction _ _) _ = LT

  -- Compare when one is a product and the other is a power, sum, factorial,
  -- function or symbol
  compare u@(Product _) v@(Power _ _) = compare u (mkProduct [v])
  compare u@(Product _) v@(Sum _) = compare u (mkProduct [v])
  compare u@(Product _) v@(Factorial _ ) = compare u (mkProduct [v])
  compare u@(Product _) v@(Function _ _) = compare u (mkProduct [v])
  compare u@(Product _) v@(Symbol _) = compare u (mkProduct [v])

-- Compare when one is a power and the other is a sum, factorial, function, or symbol
  compare u@(Power _ _) v@(Sum _) = compare u (mkPower v 1)
  compare u@(Power _ _) v@(Factorial _) = compare u (mkPower v 1)
  compare u@(Power _ _) v@(Function _ _) = compare u (mkPower v 1)
  compare u@(Power _ _) v@(Symbol _) = compare u (mkPower v 1)

  -- Compare when one is a sum and the other is a factorial, function, or symbol
  compare u@(Sum _) v@(Factorial _) = compare u (mkSum [v])
  compare u@(Sum _) v@(Function _ _) = compare u (mkSum [v])
  compare u@(Sum _) v@(Symbol _) = compare u (mkSum [v])

  -- Compare when one is a factorial and the other is a function or symbol
  compare u@(Factorial x) v@(Function _ _) =
    if x == v then EQ
    else compare u (mkFactorial v)
  compare u@(Factorial x) v@(Symbol _) =
    if x == v then EQ
    else compare u (mkFactorial v)

  -- Compare when one is a function and the other is a symbol
  compare u@(Function f _) v@(Symbol s) =
    if u == v then EQ
    else compare f s

  -- If all else fails, reverse the comparison
  -- This ensures a total order even for mixed types
  compare u v = case compare v u of
    EQ -> EQ
    LT -> GT
    GT -> LT

compareOperandList :: Operands -> Operands -> Ordering
compareOperandList xs1 xs2 = compare (NE.toList xs1) (NE.toList xs2)


