{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module RationalNumber
    ( -- * Data Types
      RNExpression (..)
    , FracOp (..)
    , SumOp (..)
    , DiffOp (..)
    , ProdOp (..)
    , PowOp (..)
    , QuotOp (..)
    , FactOp (..)
    
    -- * Pattern Synonyms
    , pattern RNeg
    , pattern (:+:)
    , pattern (:-:)
    , pattern (:*:)
    , pattern (:/:)
    , pattern (:^:)
    
    -- * Smart Constructors
    , mkInteger
    , mkFraction
    , mkFractionSafe
    , mkRational
    
    -- * Predicates
    , isUndefined
    , isInteger
    , isFraction
    
    -- * Simplification
    , simplifyRNExpression
    , simplifyRationalNumber
    
    -- * Evaluation
    , RNResult(..)
    , evaluateRNExpression
    ) where

import qualified Data.Ratio

-- ============================================================================
-- * Data Types
-- ============================================================================

-- | Result type for RN expression evaluation
data RNResult a
  = RNSuccess a
  | RNUndefined String
  | RNError String
  deriving (Eq, Show)

-- | Operator types for different kinds of operations
data FracOp = MakeFraction deriving (Eq, Show)
data SumOp = UnaryPlus | BinaryPlus deriving (Eq, Show)
data DiffOp = UnaryMinus | BinaryMinus deriving (Eq, Show)
data ProdOp = Multiply deriving (Eq, Show)
data PowOp = Power deriving (Eq, Show)
data QuotOp = Divide deriving (Eq, Show)
data FactOp = Factorial deriving (Eq, Show)

-- | Rational Number Expression (RNE) as defined in Definition 2.26
data RNExpression
  = RInteger Integer                              -- RNE-1: u is an integer
  | RFracOp FracOp Integer Integer                -- RNE-2: u is a fraction (numerator, denominator)
  | RSumOp SumOp [RNExpression]                   -- RNE-3: unary/binary sum operations
  | RDiffOp DiffOp [RNExpression]                 -- RNE-4: unary/binary difference operations
  | RProdOp ProdOp [RNExpression]                 -- RNE-5: binary product
  | RQuotOp QuotOp RNExpression RNExpression      -- RNE-6: quotient
  | RPowOp PowOp RNExpression Integer             -- RNE-7: power (base is RNE, exponent is integer)
  | RFactOp FactOp RNExpression                   -- Additional: factorial operation
  deriving (Eq, Show)

-- ============================================================================
-- * Pattern Synonyms
-- ============================================================================

pattern RNeg :: RNExpression -> RNExpression
pattern RNeg x = RDiffOp UnaryMinus [x]

pattern (:+:) :: RNExpression -> RNExpression -> RNExpression
pattern x :+: y = RSumOp BinaryPlus [x, y]

pattern (:-:) :: RNExpression -> RNExpression -> RNExpression
pattern x :-: y = RDiffOp BinaryMinus [x, y]

pattern (:*:) :: RNExpression -> RNExpression -> RNExpression
pattern x :*: y = RProdOp Multiply [x, y]

pattern (:/:) :: RNExpression -> RNExpression -> RNExpression
pattern x :/: y = RQuotOp Divide x y

pattern (:^:) :: RNExpression -> Integer -> RNExpression
pattern x :^: n = RPowOp Power x n

-- ============================================================================
-- * Smart Constructors
-- ============================================================================

mkInteger :: Integer -> RNExpression
mkInteger = RInteger

mkFraction :: Integer -> Integer -> RNExpression
mkFraction n d
  | d == 0 = RFracOp MakeFraction n d  -- Allow for later detection
  | otherwise = RFracOp MakeFraction n d

-- | Safe fraction constructor
mkFractionSafe :: Integer -> Integer -> Maybe RNExpression
mkFractionSafe n d
  | d == 0 = Nothing
  | otherwise = Just (RFracOp MakeFraction n d)

mkRational :: Rational -> RNExpression
mkRational r = RFracOp MakeFraction (Data.Ratio.numerator r) (Data.Ratio.denominator r)

-- ============================================================================
-- * Predicates and Accessors
-- ============================================================================

isUndefined :: RNExpression -> Bool
isUndefined (RFracOp _ _ 0) = True
isUndefined _ = False

isInteger :: RNExpression -> Bool
isInteger (RInteger _) = True
isInteger _ = False

isFraction :: RNExpression -> Bool
isFraction (RFracOp _ _ _) = True
isFraction _ = False

-- | Safely get numerator of an expression
getNumerator :: RNExpression -> Maybe Integer
getNumerator (RInteger n) = Just n
getNumerator (RFracOp _ n _) = Just n
getNumerator _ = Nothing

-- | Safely get denominator of an expression
getDenominator :: RNExpression -> Maybe Integer
getDenominator (RInteger _) = Just 1
getDenominator (RFracOp _ _ d) = Just d
getDenominator _ = Nothing

-- ============================================================================
-- * Type Class Instances
-- ============================================================================
instance Num RNExpression where
  (+) = (:+:)
  (-) = (:-:)
  (*) = (:*:)
  negate x = RDiffOp UnaryMinus [x]
  abs x = x  -- For now, we'll keep this simple
  signum _ = RInteger 1  -- Simplified for now
  fromInteger = RInteger

instance Fractional RNExpression where
  (/) = (:/:)
  fromRational = mkRational

-- ============================================================================
-- * Simplification Functions
-- ============================================================================

-- | Simplify a rational number (fraction or integer)
simplifyRationalNumber :: RNExpression -> RNResult RNExpression
simplifyRationalNumber = \case
  u@(RInteger _) -> RNSuccess u
  
  RFracOp _ n d
    | d == 0 -> RNUndefined "Division by zero"
    | n == 0 -> RNSuccess (RInteger 0)
    | n `mod` d == 0 -> RNSuccess (RInteger (n `div` d))
    | otherwise -> 
        let g = gcd n d
            (n', d') = if d > 0 
                      then (n `div` g, d `div` g)
                      else (negate n `div` g, negate d `div` g)
        in RNSuccess (RFracOp MakeFraction n' d')
  
  other -> RNSuccess other

-- | Main simplification function for RN expressions
simplifyRNExpression :: RNExpression -> RNResult RNExpression
simplifyRNExpression expr = 
  case simplifyStep expr of
    RNSuccess simplified -> simplifyRationalNumber simplified
    other -> other

-- | Single step of simplification
simplifyStep :: RNExpression -> RNResult RNExpression
simplifyStep = \case
  u@(RInteger _) -> RNSuccess u
  
  u@(RFracOp _ _ d)
    | d == 0 -> RNUndefined "Division by zero"
    | otherwise -> RNSuccess u
  
  RSumOp UnaryPlus [x] -> simplifyStep x
  
  RSumOp BinaryPlus [x, y] -> do
    x' <- simplifyStep x
    y' <- simplifyStep y
    evaluateSum x' y'
  
  RDiffOp UnaryMinus [x] -> do
    x' <- simplifyStep x
    evaluateProduct (RInteger (-1)) x'
  
  RDiffOp BinaryMinus [x, y] -> do
    x' <- simplifyStep x
    y' <- simplifyStep y
    evaluateDifference x' y'
  
  RProdOp _ [x, y] -> do
    x' <- simplifyStep x
    y' <- simplifyStep y
    evaluateProduct x' y'
  
  RQuotOp _ x y -> do
    x' <- simplifyStep x
    y' <- simplifyStep y
    evaluateQuotient x' y'
  
  RPowOp _ x n -> do
    x' <- simplifyStep x
    evaluatePower x' n
  
  RFactOp _ x -> do
    x' <- simplifyStep x
    RNSuccess (RFactOp Factorial x')
  
  _ -> RNError "Invalid expression structure"

-- | Evaluate the entire expression to a final result
evaluateRNExpression :: RNExpression -> RNResult RNExpression
evaluateRNExpression = simplifyRNExpression

-- ============================================================================
-- * Evaluation Helper Functions
-- ============================================================================

-- | Evaluate sum of two expressions
evaluateSum :: RNExpression -> RNExpression -> RNResult RNExpression
evaluateSum v w = do
  nv <- safeGetNumerator v
  nw <- safeGetNumerator w
  dv <- safeGetDenominator v
  dw <- safeGetDenominator w
  
  let commonDenom = dv * dw
      newNumerator = nv * dw + nw * dv
  
  RNSuccess (mkFraction newNumerator commonDenom)

-- | Evaluate difference of two expressions
evaluateDifference :: RNExpression -> RNExpression -> RNResult RNExpression
evaluateDifference v w = do
  nv <- safeGetNumerator v
  nw <- safeGetNumerator w
  dv <- safeGetDenominator v
  dw <- safeGetDenominator w
  
  let commonDenom = dv * dw
      newNumerator = nv * dw - nw * dv
  
  RNSuccess (mkFraction newNumerator commonDenom)

-- | Evaluate product of two expressions
evaluateProduct :: RNExpression -> RNExpression -> RNResult RNExpression
evaluateProduct v w = do
  nv <- safeGetNumerator v
  nw <- safeGetNumerator w
  dv <- safeGetDenominator v
  dw <- safeGetDenominator w
  
  RNSuccess (mkFraction (nv * nw) (dv * dw))

-- | Evaluate quotient of two expressions
evaluateQuotient :: RNExpression -> RNExpression -> RNResult RNExpression
evaluateQuotient v w = do
  nv <- safeGetNumerator v
  nw <- safeGetNumerator w
  dv <- safeGetDenominator v
  dw <- safeGetDenominator w
  
  if nw == 0
    then RNUndefined "Division by zero"
    else RNSuccess (mkFraction (nv * dw) (nw * dv))

-- | Evaluate power of an expression
evaluatePower :: RNExpression -> Integer -> RNResult RNExpression
evaluatePower v n = do
  vn <- safeGetNumerator v
  vd <- safeGetDenominator v
  
  if
    | vn == 0 && n >= 1 -> RNSuccess (RInteger 0)
    | vn == 0 && n <= 0 -> RNUndefined "Zero to non-positive power"
    | n > 0 -> evaluatePower v (n - 1) >>= \s -> evaluateProduct s v
    | n == 0 -> RNSuccess (RInteger 1)
    | n == -1 -> RNSuccess (mkFraction vd vn)
    | n < -1 -> evaluatePower (mkFraction vd vn) (-n)
    | otherwise -> RNError "Invalid power operation"

-- ============================================================================
-- * Safe Accessor Functions
-- ============================================================================

-- | Safely get numerator with error handling
safeGetNumerator :: RNExpression -> RNResult Integer
safeGetNumerator expr = case getNumerator expr of
  Just n -> RNSuccess n
  Nothing -> RNError ("Cannot get numerator from: " ++ show expr)

-- | Safely get denominator with error handling  
safeGetDenominator :: RNExpression -> RNResult Integer
safeGetDenominator expr = case getDenominator expr of
  Just d -> if d == 0 
           then RNUndefined "Zero denominator"
           else RNSuccess d
  Nothing -> RNError ("Cannot get denominator from: " ++ show expr)

-- ============================================================================
-- * Result Monad Instance
-- ============================================================================

instance Functor RNResult where
  fmap f (RNSuccess x) = RNSuccess (f x)
  fmap _ (RNUndefined msg) = RNUndefined msg
  fmap _ (RNError msg) = RNError msg

instance Applicative RNResult where
  pure = RNSuccess
  (RNSuccess f) <*> (RNSuccess x) = RNSuccess (f x)
  (RNUndefined msg) <*> _ = RNUndefined msg
  (RNError msg) <*> _ = RNError msg
  _ <*> (RNUndefined msg) = RNUndefined msg
  _ <*> (RNError msg) = RNError msg

instance Monad RNResult where
  return = pure
  (RNSuccess x) >>= f = f x
  (RNUndefined msg) >>= _ = RNUndefined msg
  (RNError msg) >>= _ = RNError msg
