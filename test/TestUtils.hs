{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

module TestUtils where

import           Test.Tasty.QuickCheck
import           SymHask.Symbolic
import qualified Data.List.NonEmpty as NE

-- | Use a newtype or a specific type alias if Expr takes arguments
-- Assuming UnsimplifiedExpr as the target for random generation
instance Arbitrary UnsimplifiedExpr where
    arbitrary :: Gen UnsimplifiedExpr
    arbitrary = sized arbitraryExpr
    shrink :: UnsimplifiedExpr -> [UnsimplifiedExpr]
    shrink = genericShrinkExpr

-- Define safe ranges for numbers
valInteger :: Gen Integer
valInteger = choose (-10, 10)

expInteger :: Gen Integer
expInteger = choose (0, 4) -- Verify logic with small powers like x**2, x**3

-- | Generate an expression based on size 'n' to avoid infinite recursion
arbitraryExpr :: Int -> Gen UnsimplifiedExpr
arbitraryExpr 0 = oneof
    [ mkNumber <$> valInteger
    , mkSymbol <$> elements ["x", "y", "z", "a", "b"]
    ]
arbitraryExpr n = frequency
    [ (3, arbitraryExpr 0) -- Base cases
    , (1, mkSum . NE.fromList <$> vectorOf 2 subExpr)
    , (1, mkProduct . NE.fromList <$> vectorOf 2 subExpr)
    , (1, do
        b <- subExpr
        -- Either a very small number or a complex expression (but rarely large number)
        e <- frequency
                [ (5, mkNumber <$> expInteger)
                , (1, subExpr)
                ]
        return $ mkPower b e)
    , (1, liftA2 mkFraction valInteger (valInteger `suchThat` (/= 0)))
    ]
  where
    subExpr = arbitraryExpr (n `div` 2)

-- | Custom shrinker to help debug failing tests by making expressions smaller
genericShrinkExpr :: UnsimplifiedExpr -> [UnsimplifiedExpr]
genericShrinkExpr expr = 
    case expr of
        Sum' args -> NE.toList args
        Product' args -> NE.toList args
        Power' b e -> [b, e]
        Fraction' _ _ -> [mkNumber 1] -- Shrink fraction to 1
        _ -> []