{-# LANGUAGE ScopedTypeVariables #-}

module SymHask.PolynomialSpec
  ( tests,
  )
where

import Data.List.NonEmpty (NonEmpty ((:|)))
import SymHask.Symbolic (SimplifiedExpr, UnsimplifiedExpr, mkFraction, mkFunction, mkNumber, mkSymbol)
import SymHask.Symbolic.Basic.Polynomial (isMonomialSv, isPolynomialSv)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import TestUtils (simplifyOrFail)

tests :: TestTree
tests =
  testGroup
    "Polynomial"
    [ monomialTests,
      polynomialTests
    ]

monomialTests :: TestTree
monomialTests =
  testGroup
    "isMonomial"
    [ testCase "constants are monomials" $ do
        let expr1 = mkNumber 3 :: UnsimplifiedExpr
            expr2 = mkFraction 2 5 :: UnsimplifiedExpr
        simplifyOrFail expr1 `checkMonomial` True
        simplifyOrFail expr2 `checkMonomial` True,
      testCase "the variable itself is a monomial" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        simplifyOrFail x `checkMonomial` True,
      testCase "powers with exponent greater than one are monomials" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        simplifyOrFail (x ** (3 :: UnsimplifiedExpr)) `checkMonomial` True,
      testCase "products of monomials are monomials" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        simplifyOrFail (mkNumber 2 * x * (x ** (2 :: UnsimplifiedExpr))) `checkMonomial` True,
      testCase "non-monomials are rejected" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
        simplifyOrFail (x + y) `checkMonomial` False
        simplifyOrFail (x * (x + 1)) `checkMonomial` False
        simplifyOrFail (mkFunction "sin" (x :| [])) `checkMonomial` False
    ]

polynomialTests :: TestTree
polynomialTests =
  testGroup
    "isPolynomial"
    [ testCase "monomials are polynomials" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        simplifyOrFail (x ** (4 :: UnsimplifiedExpr)) `checkPolynomial` True,
      testCase "sums of monomials are polynomials" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x ** (2 :: UnsimplifiedExpr)) + (mkNumber 3 * x) + 1
        simplifyOrFail expr `checkPolynomial` True,
      testCase "a product containing a sum is not polynomial in this structural sense" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = x * (x + 1)
        simplifyOrFail expr `checkPolynomial` False,
      testCase "sums containing a non-monomial term are rejected" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
        simplifyOrFail (x + y) `checkPolynomial` False
        simplifyOrFail (x + mkFunction "sin" (x :| [])) `checkPolynomial` False
    ]

checkMonomial :: SimplifiedExpr -> Bool -> IO ()
checkMonomial expr expected = isMonomialSv expr "x" @?= expected

checkPolynomial :: SimplifiedExpr -> Bool -> IO ()
checkPolynomial expr expected = isPolynomialSv expr "x" @?= expected