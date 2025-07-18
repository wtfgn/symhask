{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE InstanceSigs    #-}
{-# LANGUAGE PatternSynonyms #-}

module SymHask.Symbolic
    ( -- * Core Data Types
      Expression (..)
    , ExpressionResult (..)
      -- * Smart Constructors
    , mkDifference
    , mkFactorial
    , mkFraction
    , mkFunction
    , mkNumber
    , mkPower
    , mkProduct
    , mkQuotient
    , mkSum
    , mkSymbol
    , mkUndefined
      -- * Predicates
    , isConstant
    , isFraction
    , isNumber
    , isSymbol
    , isUndefined
      -- * Helper Functions
    , getConst
    , getPowerBase
    , getPowerExponent
    , getTerm
      -- * Pattern Synonyms
    , pattern (:*:)
    , pattern (:+:)
    , pattern (:-:)
    , pattern (:/:)
    , pattern (:^:)
    , pattern Abs'
    , pattern Cos'
    , pattern Exp'
    , pattern Log'
    , pattern Neg
    , pattern Signum'
    , pattern Sin'
    , pattern Sqrt'
    , pattern Tan'
    ) where

import           Control.DeepSeq  (NFData)
import           Data.Ratio       (denominator, numerator)
import           Data.String      (IsString, fromString)
import           Data.Text        (Text)
import           GHC.Generics     (Generic)
import           TextShow         (TextShow)
import           TextShow.Generic (FromGeneric (..))


-- ============================================================================
-- * Core Data Types
-- ============================================================================

-- | Unified symbolic expression type
-- This represents all kinds of mathematical expressions in the CAS
data Expression
  = Number Integer -- Numbers (integers)
  | Fraction Integer Integer -- Rational numbers (n/d)
  | Symbol Text -- Variables and constants
  | Product [Expression] -- Multiplication: a * b * c * ...
  | Sum [Expression] -- Addition: a + b + c + ...
  | Quotient Expression Expression -- Division: a / b
  | Difference [Expression] -- Subtraction: a - b - c - ...
  | Power Expression Expression -- Exponentiation: a ^ b
  | Factorial Expression -- Factorial: n!
  | Function Text [Expression] -- Function application: f(x, y, ...)
  | Undefined -- Undefined/error expressions
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
mkSum = Sum

-- | Create a product expression
mkProduct :: [Expression] -> Expression
mkProduct = Product

-- | Create a difference expression
mkDifference :: [Expression] -> Expression
mkDifference = Difference

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
mkFunction = Function

-- | Create an undefined expression
mkUndefined :: Expression
mkUndefined = Undefined

-- ============================================================================
-- * Predicates
-- ============================================================================

-- | Check if expression is undefined
isUndefined :: Expression -> Bool
isUndefined Undefined      = True
isUndefined (Fraction _ 0) = True
isUndefined _              = False

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

-- | Check if expression is a constant (number or fraction)
isConstant :: Expression -> Bool
isConstant (Number _)     = True
isConstant (Fraction _ _) = True
isConstant _              = False

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
  x - y = mkDifference [x, y]

  negate :: Expression -> Expression
  negate x = mkProduct [mkNumber (-1), x]

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
  fromRational r = mkFraction (fromInteger $ numerator r) (fromInteger $ denominator r)

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

-- | Binary arithmetic operations
pattern (:+:) :: Expression -> Expression -> Expression
pattern x :+: y = Sum [x, y]

pattern (:*:) :: Expression -> Expression -> Expression
pattern x :*: y = Product [x, y]

pattern (:-:) :: Expression -> Expression -> Expression
pattern x :-: y = Difference [x, y]

pattern (:/:) :: Expression -> Expression -> Expression
pattern x :/: y = Quotient x y

pattern (:^:) :: Expression -> Expression -> Expression
pattern x :^: y = Power x y

-- | Unary operations
pattern Neg :: Expression -> Expression
pattern Neg x = Product [Number (-1), x]

-- | Common mathematical functions
pattern Abs' :: Expression -> Expression
pattern Abs' x = Function "abs" [x]

pattern Signum' :: Expression -> Expression
pattern Signum' x = Function "signum" [x]

pattern Sqrt' :: Expression -> Expression
pattern Sqrt' x = Function "sqrt" [x]

pattern Exp' :: Expression -> Expression
pattern Exp' x = Function "exp" [x]

pattern Log' :: Expression -> Expression
pattern Log' x = Function "log" [x]

pattern Sin' :: Expression -> Expression
pattern Sin' x = Function "sin" [x]

pattern Cos' :: Expression -> Expression
pattern Cos' x = Function "cos" [x]

pattern Tan' :: Expression -> Expression
pattern Tan' x = Function "tan" [x]

-- ============================================================================
-- * Helper Functions
-- ============================================================================
getPowerBase :: Expression -> ExpressionResult Expression
getPowerBase = \case
  u@(Symbol _) -> ExpressionSuccess u
  u@(Product _) -> ExpressionSuccess u
  u@(Sum _) -> ExpressionSuccess u
  u@(Factorial _) -> ExpressionSuccess u
  u@(Function _ _) -> ExpressionSuccess u

  (Power b _) -> ExpressionSuccess b

  Number _ -> ExpressionUndefined "Power base cannot be a number"
  Fraction _ _ -> ExpressionUndefined "Power base cannot be a fraction"

  _ -> ExpressionError
    "Unsupported expression type for power base extraction, only \
    \a symbol, product, sum, factorial or function is expected."

getPowerExponent :: Expression -> ExpressionResult Expression
getPowerExponent = \case
  (Symbol _) -> ExpressionSuccess $ mkNumber 1
  (Product _) -> ExpressionSuccess $ mkNumber 1
  (Sum _) -> ExpressionSuccess $ mkNumber 1
  (Factorial _) -> ExpressionSuccess $ mkNumber 1
  (Function _ _) -> ExpressionSuccess $ mkNumber 1

  (Power _ e) -> ExpressionSuccess e

  (Number _) -> ExpressionUndefined "Power exponent cannot be a number"
  (Fraction _ _) -> ExpressionUndefined "Power exponent cannot be a fraction"

  _ -> ExpressionError
    "Unsupported expression type for power exponent extraction, only \
    \a symbol, product, sum, factorial or function is expected."

getTerm :: Expression -> ExpressionResult Expression
getTerm = \case
  u@(Symbol _) -> ExpressionSuccess $ mkProduct [u]
  u@(Sum _) -> ExpressionSuccess $ mkProduct [u]
  u@(Power _ _) -> ExpressionSuccess $ mkProduct [u]
  u@(Factorial _) -> ExpressionSuccess $ mkProduct [u]
  u@(Function _ _) -> ExpressionSuccess $ mkProduct [u]
  u@(Product (x : xs)) -> ExpressionSuccess $ if isConstant x then mkProduct xs else u

  Number _ -> ExpressionUndefined "Cannot extract term from a number"
  Fraction _ _ -> ExpressionUndefined "Cannot extract term from a fraction"

  _ -> ExpressionError
    "Unsupported expression type for term extraction, only \
    \a number, fraction, symbol, product, sum, difference, quotient, \
    \power, factorial or function is expected."

getConst :: Expression -> ExpressionResult Expression
getConst = \case
  Symbol _ -> ExpressionSuccess $ mkNumber 1
  Sum _ -> ExpressionSuccess $ mkNumber 1
  Power _ _ -> ExpressionSuccess $ mkNumber 1
  Factorial _ -> ExpressionSuccess $ mkNumber 1
  Function _ _ -> ExpressionSuccess $ mkNumber 1
  Product (x : _) -> ExpressionSuccess $ if isConstant x then x else mkNumber 1

  Number _ -> ExpressionUndefined "Cannot extract constant from a number"
  Fraction _ _ -> ExpressionUndefined "Cannot extract constant from a fraction"

  _ -> ExpressionError
    "Unsupported expression type for constant extraction, only \
    \a number, fraction, symbol, product, sum, difference, quotient, \
    \power, factorial or function is expected."


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
  compare (Product xs1) (Product xs2) = compareOperandList (reverse xs1) (reverse xs2)
  compare (Sum xs1) (Sum xs2) = compareOperandList (reverse xs1) (reverse xs2)

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

compareOperandList :: [Expression] -> [Expression] -> Ordering
compareOperandList [] [] = EQ
compareOperandList [] _  = LT
compareOperandList _  [] = GT
compareOperandList (x1:xs1) (x2:xs2) =
  case compare x1 x2 of
    EQ    -> compareOperandList xs1 xs2
    other -> other
