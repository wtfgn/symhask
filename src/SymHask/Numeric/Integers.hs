module SymHask.Numeric.Integers
    ( extendedEuclidean
    ) where

import qualified Data.List.NonEmpty as NE


-- Extended Euclidean algorithm to find integers m and n such that
-- a * m + b * n = gcd(a, b)
-- -- Returns a tuple (gcd(a, b), m, n)
extendedEuclidean :: Integer -> Integer -> (Integer, Integer, Integer)
extendedEuclidean a b =
  let (g, m, n) = go 1 0 0 1 a b
  in if g >= 0 then (g, m, n) else (-g, -m, -n)
  where
    go m0 m1 n0 n1 a' b'
      | b' == 0    = (a', m0, n0)
      | otherwise =
        let q = a' `div` b'
            r = a' `mod` b'
        in go m1 (m0 - q * m1) n1 (n0 - q * n1) b' r

-- Chinese Remainder Theorem
-- Given a list of distinct pairwise relatively prime positive integers m1, m2, ..., mn,
-- and a list of integers x1, x2, ..., xn with 0 <= xi < mi.
-- Returns the unique solution x in the range [0, M) where M = m1 * m2 * ... * mn.
-- This satisfies:
-- xi = x (mod mi) for each i = 1, 2, ..., n.
-- If the moduli are not pairwise coprime, the function returns Nothing.
chineseRemainder :: NE.NonEmpty Integer -> NE.NonEmpty Integer -> Maybe Integer
chineseRemainder mods remainders
  | length mods /= length remainders = Nothing
  | not (validateMods mods) = Nothing
  | not (validateRemainders mods remainders) = Nothing
  | otherwise =
    let (n, s) = go (NE.tail mods) (NE.tail remainders) (NE.head mods) (NE.head remainders)
    in if n == 0 then Nothing else Just (s `mod` n) -- the result is in [0, n)
  where
    go [] _  n s = (n, s)
    go _ [] n s = (n, s)
    go (m : ms) (x : xs) n s =
      let
        (_, c, d) = extendedEuclidean n m
        s' = c * n * x + d * m * s
        n' = n * m
      in go ms xs n' s'
    -- Validates that all moduli are distinct pairwise coprime.
    validateMods :: NE.NonEmpty Integer -> Bool
    validateMods ms =
      let uniqueMods = NE.toList ms
          coprimePairs = [(x, y) | x <- uniqueMods, y <- uniqueMods, x < y]
      in all (\(x, y) -> gcd x y == 1) coprimePairs
    -- Validates that all remainders xi are within the range [0, mi).
    validateRemainders :: NE.NonEmpty Integer -> NE.NonEmpty Integer -> Bool
    validateRemainders ms rs =
      let modList = NE.toList ms
          remList = NE.toList rs
      in all (\(m, r) -> r >= 0 && r < m) (zip modList remList)

-- Finds all positive and negative divisors of an integer n /= 0.
integerDivisors :: Integer -> [Integer]
integerDivisors n
  | n == 0    = []
  | otherwise =
    let absN = abs n
        posDivisors = [d | d <- [1..absN], absN `mod` d == 0]
        negDivisors = map negate posDivisors
    in posDivisors ++ negDivisors