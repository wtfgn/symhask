module SymHask.Symbolic.Factorial
    ( factorial
    ) where

import           SymHask.Symbolic (ExpressionError (..), Expression (..), ExpressionResult)
import Control.Monad.Error.Class (throwError)

-- safeFactorial :: (Floating a, RealFrac a) => a -> Either (ExpressionError Expression) a
-- safeFactorial n
--   | n < 0 = throwError $ InvalidDomain "Factorial of negative number is undefined" n
--   | abs (n - fromIntegral (round n :: Integer)) < 1e-10 =
--       let k = round n :: Integer
--       in if k >= 0 && k <= 170  -- Prevent overflow
--           then pure . fromIntegral $ product [1..k]
--           else throwError $ ArithmeticOverflow n
--   | n > 0 = pure $ gamma (n + 1)  -- Use gamma function for positive non-integers
--   | otherwise = throwError $ InvalidDomain "Factorial undefined for this input" n


factorial :: Integer -> Integer
factorial n
  | n < 0     = error "Factorial of negative number is undefined"
  | n == 0    = 1
  | otherwise = n * factorial (n - 1)

-- gamma :: (Ord a, Floating a) => a -> a
-- gamma z
--   | z < 0.5 = pi / (sin (pi * z) * gamma (1 - z))
--   | otherwise =
--     let
--       g = 7 :: Integer
--       coeffs = [0.99999999999980993, 676.5203681218851, -1259.1392167224028,
--                 771.32342877765313, -176.61502916214059, 12.507343278686905,
--                 -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7]
--       z' = z - 1
--       x = case coeffs of
--             (c0:_) -> c0 + sum [coeffs !! i / (z' + fromIntegral i) | i <- [1..8]]
--             []     -> error "Empty coefficients list in gamma function"
--       t = z' + fromIntegral g + 0.5
--     in sqrt (2 * pi) * t ** (z' + 0.5) * exp (-t) * x
