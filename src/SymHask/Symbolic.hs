{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE InstanceSigs    #-}
{-# LANGUAGE PatternSynonyms #-}

module SymHask.Symbolic
    ( BinaryFunction (..)
    , Expression (..)
    , UnaryFunction (..)
    , getBinaryFunction
    , getUnaryFunction
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
    , pattern Pi'
    , pattern Signum'
    , pattern Sin'
    , pattern Sinh'
    , pattern Sqrt'
    , pattern Tan'
    , pattern Tanh'
    ) where

import           Control.DeepSeq  (NFData)
import           Data.Ratio       (denominator, numerator)
import           Data.String      (IsString, fromString)
import           Data.Text        (Text)
import           GHC.Generics     (Generic)
import           TextShow         (TextShow)
import           TextShow.Generic (FromGeneric (..))

data Expression
  = Number Integer
  | Symbol Text
  | UnaryApply UnaryFunction Expression
  | BinaryApply BinaryFunction Expression Expression
  deriving (Eq, Generic, NFData, Read, Show)
  deriving (TextShow)
    via FromGeneric Expression


data UnaryFunction
  = Negate
  | Abs
  | Signum
  | Exp
  | Log
  | Sqrt
  | Sin
  | Cos
  | Tan
  | Asin
  | Acos
  | Atan
  | Sinh
  | Cosh
  | Tanh
  | Asinh
  | Acosh
  | Atanh
  deriving (Bounded, Enum, Eq, Generic, NFData, Read, Show)
  deriving (TextShow)
    via FromGeneric UnaryFunction

pattern Pi' :: Expression
pattern Pi' = Symbol "pi"

pattern Negate', Abs', Signum', Exp', Log', Sqrt', Sin', Cos', Tan', Asin', Acos', Atan', Sinh', Cosh', Tanh', Asinh', Acosh', Atanh' :: Expression -> Expression
pattern Negate' x = UnaryApply Negate x
pattern Abs' x = UnaryApply Abs x
pattern Signum' x = UnaryApply Signum x
pattern Exp' x = UnaryApply Exp x
pattern Log' x = UnaryApply Log x
pattern Sqrt' x = UnaryApply Sqrt x
pattern Sin' x = UnaryApply Sin x
pattern Cos' x = UnaryApply Cos x
pattern Tan' x = UnaryApply Tan x
pattern Asin' x = UnaryApply Asin x
pattern Acos' x = UnaryApply Acos x
pattern Atan' x = UnaryApply Atan x
pattern Sinh' x = UnaryApply Sinh x
pattern Cosh' x = UnaryApply Cosh x
pattern Tanh' x = UnaryApply Tanh x
pattern Asinh' x = UnaryApply Asinh x
pattern Acosh' x = UnaryApply Acosh x
pattern Atanh' x = UnaryApply Atanh x

data BinaryFunction
  = Add
  | Subtract
  | Multiply
  | Divide
  | Power
  | LogBase
  deriving (Bounded, Enum, Eq, Generic, NFData, Read, Show)
  deriving (TextShow)
    via FromGeneric BinaryFunction

pattern (:+:), (:*:), (:-:), (:/:), (:**:), LogBase' :: Expression -> Expression -> Expression
pattern x :+: y = BinaryApply Add x y
pattern x :*: y = BinaryApply Multiply x y
pattern x :-: y = BinaryApply Subtract x y
pattern x :/: y = BinaryApply Divide x y
pattern x :**: y = BinaryApply Power x y
pattern LogBase' x y = BinaryApply LogBase x y

instance IsString Expression where
  fromString :: String -> Expression
  fromString = Symbol . fromString

instance Num Expression where
  (+) :: Expression -> Expression -> Expression
  x + y = x :+: y

  (*) :: Expression -> Expression -> Expression
  x * y = x :*: y

  (-) :: Expression -> Expression -> Expression
  x - y = x :-: y

  negate :: Expression -> Expression
  negate = Negate'

  abs :: Expression -> Expression
  abs = Abs'

  signum :: Expression -> Expression
  signum = Signum'

  fromInteger :: Integer -> Expression
  fromInteger = Number

instance Fractional Expression where
  (/) :: Expression -> Expression -> Expression
  x / y = x :/: y

  fromRational :: Rational -> Expression
  fromRational r = Number (numerator r) / Number (denominator r)

instance Floating Expression where
  pi :: Expression
  pi = Symbol "pi"

  exp :: Expression -> Expression
  exp = Exp'

  log :: Expression -> Expression
  log = Log'

  sqrt :: Expression -> Expression
  sqrt = Sqrt'

  sin :: Expression -> Expression
  sin = Sin'

  cos :: Expression -> Expression
  cos = Cos'

  tan :: Expression -> Expression
  tan = Tan'

  asin :: Expression -> Expression
  asin = Asin'

  acos :: Expression -> Expression
  acos = Acos'

  atan :: Expression -> Expression
  atan = Atan'

  sinh :: Expression -> Expression
  sinh = Sinh'

  cosh :: Expression -> Expression
  cosh = Cosh'

  tanh :: Expression -> Expression
  tanh = Tanh'

  asinh :: Expression -> Expression
  asinh = Asinh'

  acosh :: Expression -> Expression
  acosh = Acosh'

  atanh :: Expression -> Expression
  atanh = Atanh'

getUnaryFunction :: (Floating a) => UnaryFunction -> (a -> a)
getUnaryFunction Negate = negate
getUnaryFunction Abs    = abs
getUnaryFunction Signum = signum
getUnaryFunction Exp    = exp
getUnaryFunction Log    = log
getUnaryFunction Sqrt   = sqrt
getUnaryFunction Sin    = sin
getUnaryFunction Cos    = cos
getUnaryFunction Tan    = tan
getUnaryFunction Asin   = asin
getUnaryFunction Acos   = acos
getUnaryFunction Atan   = atan
getUnaryFunction Sinh   = sinh
getUnaryFunction Cosh   = cosh
getUnaryFunction Tanh   = tanh
getUnaryFunction Asinh  = asinh
getUnaryFunction Acosh  = acosh
getUnaryFunction Atanh  = atanh

getBinaryFunction :: (Floating a) => BinaryFunction -> (a -> a -> a)
getBinaryFunction Add      = (+)
getBinaryFunction Multiply = (*)
getBinaryFunction Subtract = (-)
getBinaryFunction Divide   = (/)
getBinaryFunction Power    = (**)
getBinaryFunction LogBase  = logBase
