{-# LANGUAGE ScopedTypeVariables #-}

module SymHask.PolynomialSpec
    ( tests
    ) where

import qualified Data.HashSet                      as HS
import           Data.List.NonEmpty                (NonEmpty ((:|)))
import           SymHask.Symbolic                  (ExprError (..),
                                                    SimplifiedExpr,
                                                    Simplify (simplify),
                                                    UnsimplifiedExpr,
                                                    mkFraction, mkFunction,
                                                    mkNumber, mkSymbol)
import           SymHask.Symbolic.Basic.Polynomial (algebraicExpand,
                                                    coeffVarMonomial,
                                                    coefficientGpe,
                                                    coefficientSv, collectTerms,
                                                    degreeGpe, degreeMonomialSv,
                                                    degreeSv, denom,
                                                    expandMainOp, isMonomialGpe,
                                                    isMonomialSv,
                                                    isPolynomialGpe,
                                                    isPolynomialSv,
                                                    isRationalGre,
                                                    leadingCoefficientGpe,
                                                    leadingCoefficientSv, numer,
                                                    rationalExpand,
                                                    rationalVariables,
                                                    rationalise, variables)
import           Test.Tasty                        (TestTree, testGroup)
import           Test.Tasty.HUnit                  (testCase, (@?=))
import           TestUtils                         (simplifyOrFail)

tests :: TestTree
tests =
  testGroup
    "Polynomial"
    [ monomialTests
    , polynomialTests
    , degreeMonomialTests
    , degreeTests
    , coefficientTests
    , leadingCoefficientTests
    , monomialGpeTests
    , polynomialGpeTests
    , variablesTests
    , degreeGpeTests
    , coefficientGpeTests
    , leadingCoefficientGpeTests
    , algebraicExpandTests
    , collectTermsTests
    , coeffVarMonomialTests
    , denomTests
    , numerTests
    , rationalVariablesTests
    , rationaliseTests
    , rationalGreTests
    , rationalExpandTests
    , expandMainOpTests
    ]

monomialTests :: TestTree
monomialTests =
  testGroup
    "isMonomial"
    [ testCase "constants are monomials" $ do
        let expr1 = mkNumber 3 :: UnsimplifiedExpr
            expr2 = mkFraction 2 5 :: UnsimplifiedExpr
        simplifyOrFail expr1 `checkMonomial` True
        simplifyOrFail expr2 `checkMonomial` True
    , testCase "the variable itself is a monomial" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        simplifyOrFail x `checkMonomial` True
    , testCase "powers with exponent greater than one are monomials" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        simplifyOrFail (x ** (3 :: UnsimplifiedExpr)) `checkMonomial` True
    , testCase "products of monomials are monomials" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        simplifyOrFail (mkNumber 2 * x * (x ** 2)) `checkMonomial` True
    , testCase "non-monomials are rejected" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
        simplifyOrFail (x + y) `checkMonomial` False
        simplifyOrFail (x * (x + 1)) `checkMonomial` False
        simplifyOrFail (mkFunction "sin" (x :| [])) `checkMonomial` False
    , testCase "2*x^3 is a monomial" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = mkNumber 2 * (x ** (3 :: UnsimplifiedExpr))
        simplifyOrFail expr `checkMonomial` True
    , testCase "x + 1 is not a monomial" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = x + 1
        simplifyOrFail expr `checkMonomial` False
    ]

polynomialTests :: TestTree
polynomialTests =
  testGroup
    "isPolynomial"
    [ testCase "monomials are polynomials" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        simplifyOrFail (x ** (4 :: UnsimplifiedExpr)) `checkPolynomial` True
    , testCase "sums of monomials are polynomials" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x ** (2 :: UnsimplifiedExpr)) + (mkNumber 3 * x) + 1
        simplifyOrFail expr `checkPolynomial` True
    , testCase "a product containing a sum is not polynomial in this structural sense" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = x * (x + 1)
        simplifyOrFail expr `checkPolynomial` False
    , testCase "sums containing a non-monomial term are rejected" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
        simplifyOrFail (x + y) `checkPolynomial` False
        simplifyOrFail (x + mkFunction "sin" (x :| [])) `checkPolynomial` False
    , testCase "3*x^2 + 4*x + 5 is a polynomial" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (mkNumber 3 * (x ** (2 :: UnsimplifiedExpr))) + (mkNumber 4 * x) + 5
        simplifyOrFail expr `checkPolynomial` True
    , testCase "1 / (x + 1) is not a polynomial" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = 1 / (x + 1)
        simplifyOrFail expr `checkPolynomial` False
    , testCase "a*x^2 + b*x + c is not a polynomial" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            c = mkSymbol "c" :: UnsimplifiedExpr
            expr = (a * (x ** (2 :: UnsimplifiedExpr))) + (b * x) + c
        simplifyOrFail expr `checkPolynomial` False
    ]

checkMonomial :: SimplifiedExpr -> Bool -> IO ()
checkMonomial expr expected = isMonomialSv expr "x" @?= expected

checkPolynomial :: SimplifiedExpr -> Bool -> IO ()
checkPolynomial expr expected = isPolynomialSv expr "x" @?= expected

degreeMonomialTests :: TestTree
degreeMonomialTests =
  testGroup
    "degreeMonomialSv"
    [ testCase "constants have degree 0" $ do
        let expr1 = mkNumber 5 :: UnsimplifiedExpr
            expr2 = mkFraction 2 3 :: UnsimplifiedExpr
        degreeMonomialSv (simplifyOrFail expr1) "x" @?= Just 0
        degreeMonomialSv (simplifyOrFail expr2) "x" @?= Just 0
    , testCase "zero is Undefined" $ do
        let expr = mkNumber 0 :: UnsimplifiedExpr
        degreeMonomialSv (simplifyOrFail expr) "x" @?= Nothing
    , testCase "the variable itself has degree 1" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        degreeMonomialSv (simplifyOrFail x) "x" @?= Just 1
    , testCase "powers of the variable" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        degreeMonomialSv (simplifyOrFail (x ** (2 :: UnsimplifiedExpr))) "x" @?= Just 2
        degreeMonomialSv (simplifyOrFail (x ** (3 :: UnsimplifiedExpr))) "x" @?= Just 3
    , testCase "products of constants and powers" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        degreeMonomialSv (simplifyOrFail (mkNumber 2 * x)) "x" @?= Just 1
        degreeMonomialSv (simplifyOrFail (mkNumber 3 * (x ** (2 :: UnsimplifiedExpr)))) "x" @?= Just 2
    , testCase "different variables are Undefined" $ do
        let y = mkSymbol "y" :: UnsimplifiedExpr
        degreeMonomialSv (simplifyOrFail y) "x" @?= Nothing
    , testCase "sums are Undefined" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        degreeMonomialSv (simplifyOrFail (x + 1)) "x" @?= Nothing
    ]

degreeTests :: TestTree
degreeTests =
  testGroup
    "degreeSv"
    [ testCase "degree of polynomial 3x^2 + 4x + 5 is 2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (mkNumber 3 * (x ** (2 :: UnsimplifiedExpr))) + (mkNumber 4 * x) + 5
        degreeSv (simplifyOrFail expr) "x" @?= Just 2
    , testCase "degree of monomial 2x^3 is 3" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        degreeSv (simplifyOrFail (mkNumber 2 * (x ** (3 :: UnsimplifiedExpr)))) "x" @?= Just 3
    , testCase "degree of constant is 0" $ do
        degreeSv (simplifyOrFail (mkNumber 5 :: UnsimplifiedExpr)) "x" @?= Just 0
    , testCase "degree of product of sums is Undefined" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x + 1) * (x + 3)
        degreeSv (simplifyOrFail expr) "x" @?= Nothing
    , testCase "polynomial with varying degrees" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = x + (x ** (5 :: UnsimplifiedExpr)) + (mkNumber 2 * (x ** (3 :: UnsimplifiedExpr)))
        degreeSv (simplifyOrFail expr) "x" @?= Just 5
    , testCase "sum with non-polynomial term is Undefined" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        degreeSv (simplifyOrFail (x + mkFunction "sin" (x :| []))) "x" @?= Nothing
    ]

coefficientTests :: TestTree
coefficientTests =
  testGroup
    "coefficientSv"
    [ testCase "coefficient of x^1 in x^2 + 3x + 5 is 3" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x ** (2 :: UnsimplifiedExpr)) + (mkNumber 3 * x) + 5
        coefficientSv (simplifyOrFail expr) "x" 1 @?= Right (mkNumber 3)
    , testCase "coefficient of x^4 in 2x^3 + 3x is 0" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (mkNumber 2 * (x ** (3 :: UnsimplifiedExpr))) + (mkNumber 3 * x)
        coefficientSv (simplifyOrFail expr) "x" 4 @?= Right (mkNumber 0)
    , testCase "coefficient of x^0 in 3 is 3" $ do
        coefficientSv (simplifyOrFail (mkNumber 3 :: UnsimplifiedExpr)) "x" 0 @?= Right (mkNumber 3)
    , testCase "coefficient of x^2 in 2*x^2/3 + x + 1 is 2/3" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (mkFraction 2 3 * (x ** (2 :: UnsimplifiedExpr))) + x + 1
        coefficientSv (simplifyOrFail expr) "x" 2 @?= simplify (mkFraction 2 3)
    , testCase "coefficient of x^2 in (x + 1)(x + 3) returns error" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x + 1) * (x + 3)
        case coefficientSv (simplifyOrFail expr) "x" 2 of
          Left _  -> pure ()
          Right _ -> fail "Expected Left error for non-polynomial"
    ]

leadingCoefficientTests :: TestTree
leadingCoefficientTests =
  testGroup
    "leadingCoefficientSv"
    [ testCase "leading coefficient of x^2 + 3*x + 5 is 1" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x ** (2 :: UnsimplifiedExpr)) + (mkNumber 3 * x) + 5
        leadingCoefficientSv (simplifyOrFail expr) "x" @?= Right (mkNumber 1)
    , testCase "leading coefficient of 3 is 3" $ do
        leadingCoefficientSv (simplifyOrFail (mkNumber 3 :: UnsimplifiedExpr)) "x" @?= Right (mkNumber 3)
    , testCase "leading coefficient of 3*x^2 + 4*x + 5 is 3" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (mkNumber 3 * (x ** (2 :: UnsimplifiedExpr))) + (mkNumber 4 * x) + 5
        leadingCoefficientSv (simplifyOrFail expr) "x" @?= Right (mkNumber 3)
    , testCase "leading coefficient of non-polynomial returns error" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x + 1) * (x + 3)
        case leadingCoefficientSv (simplifyOrFail expr) "x" of
          Left _  -> pure ()
          Right _ -> fail "Expected Left error for non-polynomial"
    ]

monomialGpeTests :: TestTree
monomialGpeTests =
  testGroup
    "isMonomialGpe"
    [ testCase "a*x^2*y^2 is GME in {x, y}" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = a * (x ** (2 :: UnsimplifiedExpr)) * (y ** (2 :: UnsimplifiedExpr))
        isMonomialGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x, simplifyOrFail y]) @?= True
    , testCase "x^2 + y^2 is not GME in {x, y}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = (x ** (2 :: UnsimplifiedExpr)) + (y ** (2 :: UnsimplifiedExpr))
        isMonomialGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x, simplifyOrFail y]) @?= False
    , testCase "x is GME in {x}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        isMonomialGpe (simplifyOrFail x) (HS.fromList [simplifyOrFail x]) @?= True
    , testCase "x^3 is GME in {x}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = x ** (3 :: UnsimplifiedExpr)
        isMonomialGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x]) @?= True
    , testCase "3 is GME in {x} (free of x)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        isMonomialGpe (simplifyOrFail (mkNumber 3 :: UnsimplifiedExpr)) (HS.fromList [simplifyOrFail x]) @?= True
    ]

polynomialGpeTests :: TestTree
polynomialGpeTests =
  testGroup
    "isPolynomialGpe"
    [ testCase "x^2 + y^2 is GPE in {x, y}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = (x ** (2 :: UnsimplifiedExpr)) + (y ** (2 :: UnsimplifiedExpr))
        isPolynomialGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x, simplifyOrFail y]) @?= True
    , testCase "sin^2(x) + 2*sin(x) + 3 is GPE in {sin(x)}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            sinx = mkFunction "sin" (x :| []) :: UnsimplifiedExpr
            expr = (sinx ** (2 :: UnsimplifiedExpr)) + (mkNumber 2 * sinx) + 3
        isPolynomialGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail sinx]) @?= True
    , testCase "x/y + 2*y is not GPE in {x, y}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = (x / y) + (mkNumber 2 * y)
        isPolynomialGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x, simplifyOrFail y]) @?= False
    , testCase "(x + 1)*(x + 3) is not GPE in {x}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x + 1) * (x + 3)
        isPolynomialGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x]) @?= False
    , testCase "3 is GPE in {x}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        isPolynomialGpe (simplifyOrFail (mkNumber 3 :: UnsimplifiedExpr)) (HS.fromList [simplifyOrFail x]) @?= True
    , testCase "a + b is GPE in {a + b}" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            expr = a + b
        isPolynomialGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail expr]) @?= True
    , testCase "3*w*x^2*y^3*z^4 is GPE in {x, z}" $ do
        let w = mkSymbol "w" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            z = mkSymbol "z" :: UnsimplifiedExpr
            expr = mkNumber 3 * w * (x ** (2 :: UnsimplifiedExpr)) * (y ** (3 :: UnsimplifiedExpr)) * (z ** (4 :: UnsimplifiedExpr))
        isPolynomialGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x, simplifyOrFail z]) @?= True
    , testCase "a*(x^2 + 1)^2 + (x^2 + 1) is GPE in {x^2 + 1}" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            x2Plus1 = (x ** (2 :: UnsimplifiedExpr)) + 1
            expr = a * (x2Plus1 ** (2 :: UnsimplifiedExpr)) + x2Plus1
        isPolynomialGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x2Plus1]) @?= True
    , testCase "x*(x^2 + 1) is NOT GPE in {x}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = x * ((x ** (2 :: UnsimplifiedExpr)) + 1)
        isPolynomialGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x]) @?= False
    , testCase "y^2*(y^4 + 1) is GPE in {y^2}" $ do
        let y = mkSymbol "y" :: UnsimplifiedExpr
            expr = (y ** (2 :: UnsimplifiedExpr)) * ((y ** (4 :: UnsimplifiedExpr)) + 1)
        isPolynomialGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail (y ** (2 :: UnsimplifiedExpr))]) @?= True
    , testCase "2*(x^2)^2 + 3*(x^2) is GPE in {x^2}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            x2 = x ** (2 :: UnsimplifiedExpr)
            expr = mkNumber 2 * (x2 ** (2 :: UnsimplifiedExpr)) + mkNumber 3 * x2
        isPolynomialGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x2]) @?= True
    ]

variablesTests :: TestTree
variablesTests =
  testGroup
    "variables"
    [ testCase "Variables(x^3 + 3 x^2 y + 3 x y^2 + y^3) -> {x,y}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = (x ** (3 :: UnsimplifiedExpr)) + (mkNumber 3 * (x ** (2 :: UnsimplifiedExpr)) * y) + (mkNumber 3 * x * (y ** (2 :: UnsimplifiedExpr))) + (y ** (3 :: UnsimplifiedExpr))
        variables (simplifyOrFail expr) @?= HS.fromList [mkSymbol "x", mkSymbol "y"]
    , testCase "Variables(3*x*(a+1)*y^2*z^n) -> {x, a+1, y, z^n}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            z = mkSymbol "z" :: UnsimplifiedExpr
            n = mkSymbol "n" :: UnsimplifiedExpr
            a = mkSymbol "a" :: UnsimplifiedExpr
            expr = mkNumber 3 * x * (a + 1) * (y ** (2 :: UnsimplifiedExpr)) * (z ** n)
        variables (simplifyOrFail expr) @?= HS.fromList [mkSymbol "x", simplifyOrFail (a + 1), mkSymbol "y", simplifyOrFail (z ** n)]
    , testCase "Variables(a*sin^2(x) + 2*b*sin(x) + 3*c) -> {a,b,c,sin(x)}" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            c = mkSymbol "c" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            expr = a * (mkFunction "sin" (x :| []) ** (2 :: UnsimplifiedExpr)) + mkNumber 2 * b * mkFunction "sin" (x :| []) + mkNumber 3 * c
        variables (simplifyOrFail expr) @?= HS.fromList [simplifyOrFail (mkFunction "sin" (x :| [])), mkSymbol "a", mkSymbol "b", mkSymbol "c"]
    , testCase "Variables(1/2) -> empty" $ do
        variables (simplifyOrFail (mkFraction 1 2 :: UnsimplifiedExpr)) @?= HS.empty
    , testCase "Variables(sqrt2*x^2 + sqrt3*x + sqrt5) -> {x, sqrt2, sqrt3, sqrt5}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            sqrt2 = mkFunction "sqrt" (mkNumber 2 :| []) :: UnsimplifiedExpr
            sqrt3 = mkFunction "sqrt" (mkNumber 3 :| []) :: UnsimplifiedExpr
            sqrt5 = mkFunction "sqrt" (mkNumber 5 :| []) :: UnsimplifiedExpr
            expr = simplifyOrFail (sqrt2 * (x ** (2 :: UnsimplifiedExpr)) + sqrt3 * x + sqrt5)
        variables expr @?= HS.fromList [mkSymbol "x", simplifyOrFail sqrt2, simplifyOrFail sqrt3, simplifyOrFail sqrt5]
    ]

degreeGpeTests :: TestTree
degreeGpeTests =
  testGroup
    "degreeGpe"
    [ testCase "degree of a*x^2*y^2 in {x,y} is 4" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = a * (x ** (2 :: UnsimplifiedExpr)) * (y ** (2 :: UnsimplifiedExpr))
        degreeGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x, simplifyOrFail y]) @?= Right (Just 4)
    , testCase "degree of 3*w*x^2*y^3*z^4 in {x, z} is 6" $ do
        let w = mkSymbol "w" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            z = mkSymbol "z" :: UnsimplifiedExpr
            expr = mkNumber 3 * w * (x ** (2 :: UnsimplifiedExpr)) * (y ** (3 :: UnsimplifiedExpr)) * (z ** (4 :: UnsimplifiedExpr))
        degreeGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x, simplifyOrFail z]) @?= Right (Just 6)
    , testCase "degree of x^2 + y^2 in {x,y} is 2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = (x ** (2 :: UnsimplifiedExpr)) + (y ** (2 :: UnsimplifiedExpr))
        degreeGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x, simplifyOrFail y]) @?= Right (Just 2)
    , testCase "degree of a*sin(x)^2 + b*sin(x) + c in {sin(x)} is 2" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            c = mkSymbol "c" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            expr = a * (mkFunction "sin" (x :| []) ** (2 :: UnsimplifiedExpr)) + mkNumber 2 * b * mkFunction "sin" (x :| []) + mkNumber 3 * c
        degreeGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail (mkFunction "sin" (x :| []))]) @?= Right (Just 2)
    , testCase "degree of 2*x^2*y*z^3 + w*x*z^6 in {x, z} is 7" $ do
        let w = mkSymbol "w" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            z = mkSymbol "z" :: UnsimplifiedExpr
            expr = (mkNumber 2 * (x ** (2 :: UnsimplifiedExpr)) * y * (z ** (3 :: UnsimplifiedExpr))) + (w * x * (z ** (6 :: UnsimplifiedExpr)))
        degreeGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x, simplifyOrFail z]) @?= Right (Just 7)
    , testCase "degree of zero monomial is -infinity (Nothing)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        degreeGpe (simplifyOrFail (mkNumber 0 :: UnsimplifiedExpr)) (HS.fromList [simplifyOrFail x]) @?= Right Nothing
    , testCase "degreeGpe errors on non-GPE" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x + 1) * (x + 3)
        case degreeGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x]) of
          Left UnsupportedOperation{} -> pure ()
          _ -> fail "Expected Left UnsupportedOperation for non-GPE"
    , testCase "degree of a*(x^2 + 1)^2 + (x^2 + 1) in {x^2 + 1} is 2" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            x2Plus1 = (x ** (2 :: UnsimplifiedExpr)) + 1
            expr = a * (x2Plus1 ** (2 :: UnsimplifiedExpr)) + x2Plus1
        degreeGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x2Plus1]) @?= Right (Just 2)
    , testCase "degree of 2*(x^2)^2 + 3*(x^2) in {x^2} is 1" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            x2 = x ** (2 :: UnsimplifiedExpr)
            expr = mkNumber 2 * (x2 ** (2 :: UnsimplifiedExpr)) + mkNumber 3 * x2
        degreeGpe (simplifyOrFail expr) (HS.fromList [simplifyOrFail x2]) @?= Right (Just 1)
    ]

coefficientGpeTests :: TestTree
coefficientGpeTests =
  testGroup
    "coefficientGpe"
    [ testCase "coefficient of a*x^2 + b*x + c in x^2 is a" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            c = mkSymbol "c" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (a * (x ** (2 :: UnsimplifiedExpr))) + (b * x) + c
        coefficientGpe (simplifyOrFail expr) (simplifyOrFail x) 2 @?= Right (simplifyOrFail a)
    , testCase "coefficient of 3*x*y^2 + 5*x^2*y + 7*x + 9 in x is 3*y^2 + 7" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = mkNumber 3 * x * (y ** (2 :: UnsimplifiedExpr)) + mkNumber 5 * (x ** (2 :: UnsimplifiedExpr)) * y + mkNumber 7 * x + mkNumber 9
            expected = mkNumber 3 * (y ** (2 :: UnsimplifiedExpr)) + mkNumber 7
        coefficientGpe (simplifyOrFail expr) (simplifyOrFail x) 1 @?= Right (simplifyOrFail expected)
    , testCase "coefficient of 3*x*y^2 + 5*x^2*y + 7*x + 9 in x^3 is 0" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = mkNumber 3 * x * (y ** (2 :: UnsimplifiedExpr)) + mkNumber 5 * (x ** (2 :: UnsimplifiedExpr)) * y + mkNumber 7 * x + mkNumber 9
            expected = mkNumber 0
        coefficientGpe (simplifyOrFail expr) (simplifyOrFail x) 3 @?= Right (simplifyOrFail expected)
    , testCase "coefficient of x^3 when absent is 0" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = mkNumber 3 * x * (y ** (2 :: UnsimplifiedExpr)) + mkNumber 5 * (x ** (2 :: UnsimplifiedExpr)) * y + mkNumber 7 * x + mkNumber 9
        coefficientGpe (simplifyOrFail expr) (simplifyOrFail x) 3 @?= Right (mkNumber 0)
    , testCase "coefficient of 3*x*y^2 + 5*x^2*y + 7*x + 9 in x*y^2 is 3" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = mkNumber 3 * x * (y ** (2 :: UnsimplifiedExpr)) + mkNumber 5 * (x ** (2 :: UnsimplifiedExpr)) * y + mkNumber 7 * x + mkNumber 9
            expected = mkNumber 3
        case coefficientGpe (simplifyOrFail expr) (simplifyOrFail x) 1 of
          Right inner -> coefficientGpe inner (simplifyOrFail y) 2 @?= Right (simplifyOrFail expected)
          Left _ -> fail "Expected Right from first coefficientGpe"
    , testCase "coefficient of 3*sin(x)*x^2 + 2*log(x)*x +4 in log(x)*x is 2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            sinX = mkFunction "sin" (x :| []) :: UnsimplifiedExpr
            logX = mkFunction "log" (x :| []) :: UnsimplifiedExpr
            expr = 3 * sinX * x ** 2 + 2 * logX * x + 4
        case coefficientGpe (simplifyOrFail expr) (simplifyOrFail logX) 1 of
          Right inner -> coefficientGpe inner (simplifyOrFail x) 1 @?= Right (mkNumber 2)
          Left _ -> fail "Expected Right from first coefficientGpe"
    , testCase "coefficient of x in x is 1" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        coefficientGpe (simplifyOrFail x) (simplifyOrFail x) 1 @?= Right (mkNumber 1)
    , testCase "coefficientGpe returns error for non-polynomial term" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            sinX = mkFunction "sin" (x :| []) :: UnsimplifiedExpr
            logX = mkFunction "log" (x :| []) :: UnsimplifiedExpr
            expr = 3 * sinX * (x ** 2) + 2 * logX * x + 4
        case coefficientGpe (simplifyOrFail expr) (simplifyOrFail x) 2 of
          Left _  -> pure ()
          Right _ -> fail "Expected Left error for non-polynomial"
    , testCase "coefficient of a*(x^2 + 1)^2 + (x^2 + 1) in {x^2 + 1} at j=2 is a" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            x2Plus1 = (x ** (2 :: UnsimplifiedExpr)) + 1
            expr = a * (x2Plus1 ** (2 :: UnsimplifiedExpr)) + x2Plus1
        coefficientGpe (simplifyOrFail expr) (simplifyOrFail x2Plus1) 2 @?= Right (simplifyOrFail a)
    , testCase "coefficient of a*(x^2 + 1)^2 + (x^2 + 1) in {x^2 + 1} at j=1 is 0" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            x2Plus1 = (x ** (2 :: UnsimplifiedExpr)) + 1
            expr = a * (x2Plus1 ** (2 :: UnsimplifiedExpr)) + x2Plus1
        coefficientGpe (simplifyOrFail expr) (simplifyOrFail x2Plus1) 1 @?= Right (simplifyOrFail 0)
    , testCase "coefficient of a*(x^2 + 1)^2 + (x^2 + 1) in {x^2 + 1} at j=0 is x^2 + 1" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            x2Plus1 = (x ** (2 :: UnsimplifiedExpr)) + 1
            expr = a * (x2Plus1 ** (2 :: UnsimplifiedExpr)) + x2Plus1
        coefficientGpe (simplifyOrFail expr) (simplifyOrFail x2Plus1) 0 @?= Right (simplifyOrFail x2Plus1)
    , testCase "coefficient of 2*(x^2)^2 + 3*(x^2) in {x^2} at j=2 is 0" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            x2 = x ** (2 :: UnsimplifiedExpr)
            expr = mkNumber 2 * (x2 ** (2 :: UnsimplifiedExpr)) + mkNumber 3 * x2
        coefficientGpe (simplifyOrFail expr) (simplifyOrFail x2) 2 @?= Right (mkNumber 0)
    , testCase "coefficient of 2*(x^2)^2 + 3*(x^2) in {x^2} at j=1 is 3" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            x2 = x ** (2 :: UnsimplifiedExpr)
            expr = mkNumber 2 * (x2 ** (2 :: UnsimplifiedExpr)) + mkNumber 3 * x2
        coefficientGpe (simplifyOrFail expr) (simplifyOrFail x2) 1 @?= Right (mkNumber 3)
    , testCase "coefficient of 2*(x^2)^2 + 3*(x^2) in {x^2} at j=0 is 2*x^4" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            x2 = x ** (2 :: UnsimplifiedExpr)
            expr = mkNumber 2 * (x2 ** (2 :: UnsimplifiedExpr)) + mkNumber 3 * x2
        coefficientGpe (simplifyOrFail expr) (simplifyOrFail x2) 0 @?= Right (simplifyOrFail (mkNumber 2 * (x2 ** (2 :: UnsimplifiedExpr))))
    ]

leadingCoefficientGpeTests :: TestTree
leadingCoefficientGpeTests =
  testGroup
    "leadingCoefficientGpe"
    [ testCase "leading coefficient of a*x^2 + b*x + c in x is a" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            c = mkSymbol "c" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (a * (x ** (2 :: UnsimplifiedExpr))) + (b * x) + c
        leadingCoefficientGpe (simplifyOrFail expr) (simplifyOrFail x) @?= Right (simplifyOrFail a)
    , testCase "leading coefficient of 3*x*y^2 + 5*x^2*y + 7*x + 9 in x is 5*y" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = mkNumber 3 * x * (y ** (2 :: UnsimplifiedExpr)) + mkNumber 5 * (x ** (2 :: UnsimplifiedExpr)) * y + mkNumber 7 * x + mkNumber 9
            expected = mkNumber 5 * (y ** (1 :: UnsimplifiedExpr))
        leadingCoefficientGpe (simplifyOrFail expr) (simplifyOrFail x) @?= Right (simplifyOrFail expected)
    , testCase "leading coefficient of 3*x*y^2 + 5*x^2*y + 7*x^2*y^3 + 9 in x is 5*y + 7*y^3" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = mkNumber 3 * x * (y ** (2 :: UnsimplifiedExpr)) + mkNumber 5 * (x ** (2 :: UnsimplifiedExpr)) * y + mkNumber 7 * (x ** (2 :: UnsimplifiedExpr)) * (y ** (3 :: UnsimplifiedExpr)) + mkNumber 9
            expected = mkNumber 5 * (y ** (1 :: UnsimplifiedExpr)) + mkNumber 7 * (y ** (3 :: UnsimplifiedExpr))
        leadingCoefficientGpe (simplifyOrFail expr) (simplifyOrFail x) @?= Right (simplifyOrFail expected)
    , testCase "leading coefficient of constant 3 is 3" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        leadingCoefficientGpe (simplifyOrFail (mkNumber 3 :: UnsimplifiedExpr)) (simplifyOrFail x) @?= Right (mkNumber 3)
    , testCase "leading coefficient of zero is 0" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        leadingCoefficientGpe (simplifyOrFail (mkNumber 0 :: UnsimplifiedExpr)) (simplifyOrFail x) @?= Right (mkNumber 0)
    , testCase "leadingCoefficientGpe errors on non-GPE" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x + 1) * (x + 3)
        case leadingCoefficientGpe (simplifyOrFail expr) (simplifyOrFail x) of
          Left UnsupportedOperation{} -> pure ()
          _ -> fail "Expected Left UnsupportedOperation for non-GPE"
    ]

coeffVarMonomialTests :: TestTree
coeffVarMonomialTests =
  testGroup
    "coeffVarMonomial"
    [ testCase "constant returns (constant,1)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        coeffVarMonomial (simplifyOrFail (mkNumber 3 :: UnsimplifiedExpr)) (HS.fromList [simplifyOrFail x]) @?= Right (mkNumber 3, mkNumber 1)
    , testCase "a * x^2 returns (a, x^2)" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            expr = simplifyOrFail (a * (x ** (2 :: UnsimplifiedExpr)))
        coeffVarMonomial expr (HS.fromList [simplifyOrFail x]) @?= Right (simplifyOrFail a, simplifyOrFail (x ** (2 :: UnsimplifiedExpr)))
    , testCase "3*x*y^2 with vars {x,y} returns (3, x*y^2)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = simplifyOrFail (mkNumber 3 * x * (y ** (2 :: UnsimplifiedExpr)))
        coeffVarMonomial expr (HS.fromList [simplifyOrFail x, simplifyOrFail y]) @?= Right (mkNumber 3, simplifyOrFail (x * (y ** (2 :: UnsimplifiedExpr))))
    , testCase " x^4 with vars {x^2} returns (x^4, 1)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = simplifyOrFail (x ** (4 :: UnsimplifiedExpr))
        coeffVarMonomial expr (HS.fromList [simplifyOrFail (x ** (2 :: UnsimplifiedExpr))]) @?= Right (simplifyOrFail (x ** (4 :: UnsimplifiedExpr)), mkNumber 1)
    , testCase "variable itself returns (1, x)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        coeffVarMonomial (simplifyOrFail x) (HS.fromList [simplifyOrFail x]) @?= Right (mkNumber 1, simplifyOrFail x)
    , testCase "free-of-variable monomial returns (monomial,1)" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            expr = simplifyOrFail (mkNumber 3 * a)
        coeffVarMonomial expr (HS.fromList [simplifyOrFail x]) @?= Right (expr, mkNumber 1)
    ]

collectTermsTests :: TestTree
collectTermsTests =
  testGroup
    "collectTerms"
    [ testCase "Collected form of 2*a*x*y + 3*b*x*y + 4*a*x + 5*b*x in {x, y} is (2*a + 3*b)*x*y + (4*a + 5*b)*x" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = mkNumber 2 * a * x * y + mkNumber 3 * b * x * y + mkNumber 4 * a * x + mkNumber 5 * b * x
            expected = (mkNumber 2 * a + mkNumber 3 * b) * x * y + (mkNumber 4 * a + mkNumber 5 * b) * x
        collectTerms (simplifyOrFail expr) (HS.fromList [simplifyOrFail x, simplifyOrFail y]) @?= Right (simplifyOrFail expected)
    , testCase "Collected form of 2*a*x*y + 3*b*x*y + 4*a*x + 5*b*x in {a, b} is (2*x*y + 4*x)*a + (3*x*y + 5*x)*b" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = mkNumber 2 * a * x * y + mkNumber 3 * b * x * y + mkNumber 4 * a * x + mkNumber 5 * b * x
            expected = (mkNumber 2 * x * y + mkNumber 4 * x) * a + (mkNumber 3 * x * y + mkNumber 5 * x) * b
        collectTerms (simplifyOrFail expr) (HS.fromList [simplifyOrFail a, simplifyOrFail b]) @?= Right (simplifyOrFail expected)
    , testCase "Collect simple like terms 2*x + 3*x + 4 in {x} -> 5*x + 4" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = mkNumber 2 * x + mkNumber 3 * x + mkNumber 4
            expected = mkNumber 5 * x + mkNumber 4
        collectTerms (simplifyOrFail expr) (HS.fromList [simplifyOrFail x]) @?= Right (simplifyOrFail expected)
    , testCase "Collect cancelling terms a*x - a*x + b in {x} -> b" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            expr = a * x + (mkNumber (-1) * a * x) + b
        collectTerms (simplifyOrFail expr) (HS.fromList [simplifyOrFail x]) @?= Right (simplifyOrFail b)
    , testCase "Collect with generalized variable x^2: 2*(x^2)^2 + 3*(x^2) in {x^2} keeps distinct parts" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            x2 = x ** (2 :: UnsimplifiedExpr)
            expr = mkNumber 2 * (x2 ** (2 :: UnsimplifiedExpr)) + mkNumber 3 * x2
        collectTerms (simplifyOrFail expr) (HS.fromList [simplifyOrFail x2]) @?= Right (simplifyOrFail expr)
    , testCase "Collected form of a*x*sin(x)*x + b in {x} does not exist because it is not a polynomial in x" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            expr = a * x * mkFunction "sin" (x :| []) * x + b
        case collectTerms (simplifyOrFail expr) (HS.fromList [simplifyOrFail x]) of
          Left _  -> pure ()
          Right _ -> fail "Expected Left error for non-polynomial"
    , testCase "Collected form of 2*a*x + 3*a*x*b in {a, x} is (2 + 3*b)*a*x" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            expr = mkNumber 2 * a * x + mkNumber 3 * a * x * b
            expected = (mkNumber 2 + mkNumber 3 * b) * a * x
        collectTerms (simplifyOrFail expr) (HS.fromList [simplifyOrFail a, simplifyOrFail x]) @?= Right (simplifyOrFail expected)
    ]

algebraicExpandTests :: TestTree
algebraicExpandTests =
  testGroup
    "algebraicExpand"
    [ testCase "(x+2)(x+3)(x+4) expands to x^3 + 9*x^2 + 26*x + 24" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x + mkNumber 2) * (x + mkNumber 3) * (x + mkNumber 4)
            expected = (x ** (3 :: UnsimplifiedExpr)) + (mkNumber 9 * (x ** (2 :: UnsimplifiedExpr))) + (mkNumber 26 * x) + mkNumber 24
        case algebraicExpand (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "algebraicExpand failed: " ++ show e
    , testCase "(x+y+z)^3 expands to x^3 + y^3 + z^3 + 3*x^2*y + 3*x^2*z + 3*y^2*x + 3*y^2*z + 3*z^2*x + 3*z^2*y + 6*x*y*z" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            z = mkSymbol "z" :: UnsimplifiedExpr
            expr = (x + y + z) ** (3 :: UnsimplifiedExpr)
            expected = x ** 3 + y ** 3 + z ** 3 + 3 * (x ** 2) * y + 3 * (x ** 2) * z + 3 * (y ** 2) * x + 3 * (y ** 2) * z + 3 * (z ** 2) * x + 3 * (z ** 2) * y + 6 * x * y * z
        case algebraicExpand (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "algebraicExpand failed: " ++ show e
    , testCase "(x+1)^2 + (y+1)^2 expands to x^2 + 2x + y^2 + 2y + 2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = (x + mkNumber 1) ** (2 :: UnsimplifiedExpr) + (y + mkNumber 1) ** (2 :: UnsimplifiedExpr)
            expected = (x ** (2 :: UnsimplifiedExpr)) + (mkNumber 2 * x) + (y ** (2 :: UnsimplifiedExpr)) + (mkNumber 2 * y) + mkNumber 2
        case algebraicExpand (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "algebraicExpand failed: " ++ show e
    , testCase "((x+2)^2 + 3)^2 expands to x^4 + 8*x^3 + 30*x^2 + 56*x + 49" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            inner = (x + mkNumber 2) ** (2 :: UnsimplifiedExpr) + mkNumber 3
            expr = inner ** (2 :: UnsimplifiedExpr)
            expected = (x ** (4 :: UnsimplifiedExpr)) + (mkNumber 8 * (x ** (3 :: UnsimplifiedExpr))) + (mkNumber 30 * (x ** (2 :: UnsimplifiedExpr))) + (mkNumber 56 * x) + mkNumber 49
        case algebraicExpand (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "algebraicExpand failed: " ++ show e
    , testCase "(x(y+1)^(3/2) + 1)(x(y+1)^(3/2) - 1) expands to x^2*y^3 + 3*x^2*y^2 + 3*x^2*y + x^2 - 1" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            yPlus1 = y + mkNumber 1
            -- x(y+1)^(3/2)
            term = x * (yPlus1 ** mkFraction 3 2)
            expr = (term + mkNumber 1) * (term - mkNumber 1)
        case algebraicExpand (simplifyOrFail expr) of
          Right out -> do
            -- The result should expand fully and be free of fractional exponents in standard form
            -- When (y+1)^3 is expanded, we get y^3 + 3y^2 + 3y + 1
            -- So x^2(y+1)^3 expands to x^2(y^3 + 3y^2 + 3y + 1)
            let expected = x ** 2 * y ** 3 + 3 * x ** 2 * y ** 2 + 3 * x ** 2 * y + x ** 2 - 1
            out @?= simplifyOrFail expected
          Left e -> fail $ "algebraicExpand failed: " ++ show e
    , testCase "((x(y+1)^(1/2) + 1)^4) expands correctly" $ do
        let x = mkSymbol "x"
            y = mkSymbol "y"
            yPlus1 = y + 1
            expr = (x * (yPlus1 ** mkFraction 1 2) + 1) ** 4
        case algebraicExpand (simplifyOrFail expr) of
          Right out -> do
            let expected =
                  (x ** 4) * (y ** 2)
                    + 2 * x ** 4 * y
                    + x ** 4
                    -- The term 4 * (x ** 3) * (yPlus1 ** (3 / 2))
                    -- with fractional exponent should be fully expanded
                    + 4 * (x ** 3) * (yPlus1 ** (1 / 2))
                    + 4 * (x ** 3) * y * (yPlus1 ** (1 / 2))
                    + 6 * (x ** 2) * y
                    + 6 * (x ** 2)
                    + 4 * x * (yPlus1 ** (1 / 2))
                    + 1
            out @?= simplifyOrFail expected
          Left e -> fail $ "algebraicExpand failed: " ++ show e
    , testCase "sin(a*(b + c)) expands to sin(a*b + a*c)" $ do
        let a = mkSymbol "a"
            b = mkSymbol "b"
            c = mkSymbol "c"
            expr = mkFunction "sin" (a * (b + c) :| [])
            expected = mkFunction "sin" (a * b + a * c :| [])
        case algebraicExpand (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "algebraicExpand failed: " ++ show e
    , testCase "sin((x(y+1)^(1/2) + 1)^4 + log(a*(x+1))) " $ do
        let x = mkSymbol "x"
            y = mkSymbol "y"
            a = mkSymbol "a"
            yPlus1 = y + 1
            inner = (x * (yPlus1 ** mkFraction 1 2) + 1) ** 4 + mkFunction "log" (a * (x + 1) :| [])
            expr = mkFunction "sin" (inner :| [])
        case algebraicExpand (simplifyOrFail expr) of
          Right out -> do
            let expectedInner =
                  (x ** 4) * (y ** 2)
                    + 2 * x ** 4 * y
                    + x ** 4
                    -- The term 4 * (x ** 3) * (yPlus1 ** (3 / 2))
                    -- with fractional exponent should be fully expanded
                    + 4 * (x ** 3) * (yPlus1 ** (1 / 2))
                    + 4 * (x ** 3) * y * (yPlus1 ** (1 / 2))
                    + 6 * (x ** 2) * y
                    + 6 * (x ** 2)
                    + 4 * x * (yPlus1 ** (1 / 2))
                    + 1
                    + mkFunction "log" (a * x + a :| [])
                expected = mkFunction "sin" (expectedInner :| [])
            out @?= simplifyOrFail expected
          Left e -> fail $ "algebraicExpand failed: " ++ show e
    , testCase "a / (b*( c + d)) expands to a / (b*c + b*d)" $ do
        let a = mkSymbol "a"
            b = mkSymbol "b"
            c = mkSymbol "c"
            d = mkSymbol "d"
            expr = a / (b * (c + d))
            expected = a / (b * c + b * d)
        case algebraicExpand (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "algebraicExpand failed: " ++ show e
    , testCase "a / ((x+1)*(x+2)) expands to a / (x^2 + 3*x + 2)" $ do
        let a = mkSymbol "a"
            x = mkSymbol "x"
            expr = a / ((x + 1) * (x + 2))
            expected = a / (x ** 2 + 3 * x + 2)
        case algebraicExpand (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "algebraicExpand failed: " ++ show e
    , testCase "1 / (x^2 + x - x*(x + 1)) returns error because of division by zero" $ do
        let x = mkSymbol "x"
            expr = 1 / (x ** 2 + x - x * (x + 1))
        case algebraicExpand (simplifyOrFail expr) of
          Left _  -> pure ()
          Right _ -> fail "Expected Left error for division by zero"
    , testCase "(x + 1)^(5/2) expands to (x + 1)^(1/2)*x^2 + 2(x + 1)^(1/2)*x + (x + 1)^(1/2)" $ do
        let x = mkSymbol "x"
            expr = (x + 1) ** mkFraction 5 2
            expected = (x + 1) ** mkFraction 1 2 * (x ** 2) + 2 * (x + 1) ** mkFraction 1 2 * x + (x + 1) ** mkFraction 1 2
        case algebraicExpand (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "algebraicExpand failed: " ++ show e
    ]

numerTests :: TestTree
numerTests =
  testGroup
    "numer"
    [ testCase "numer of (x^2 + 1)/(x + 1) is x^2 + 1" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x ** (2 :: UnsimplifiedExpr) + mkNumber 1) / (x + mkNumber 1)
            expected = x ** (2 :: UnsimplifiedExpr) + mkNumber 1
        case numer (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "numer failed: " ++ show e
    , testCase "numer of 1/(x^2 + 1) is 1" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = mkNumber 1 / (x ** (2 :: UnsimplifiedExpr) + mkNumber 1)
            expected = mkNumber 1
        case numer (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "numer failed: " ++ show e
    , testCase "numer of (x^3 + x^2 + x + 1)/(x^2 + 1) is x^3 + x^2 + x + 1" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x ** (3 :: UnsimplifiedExpr) + x ** (2 :: UnsimplifiedExpr) + x + mkNumber 1) / (x ** (2 :: UnsimplifiedExpr) + mkNumber 1)
            expected = x ** (3 :: UnsimplifiedExpr) + x ** (2 :: UnsimplifiedExpr) + x + mkNumber 1
        case numer (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "numer failed: " ++ show e
    , testCase "numer of sin(x)/cos(x) is sin(x)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = mkFunction "sin" (x :| []) / mkFunction "cos" (x :| [])
            expected = mkFunction "sin" (x :| [])
        case numer (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "numer failed: " ++ show e
    , testCase "numer of 1/sin(x) is 1" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = mkNumber 1 / mkFunction "sin" (x :| [])
            expected = mkNumber 1
        case numer (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "numer failed: " ++ show e
    , testCase "numer of (2/3)*((x*(x + 1))/(x + 2))*y^n is 2*x*(x + 1)*y^n" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            n = mkSymbol "n" :: UnsimplifiedExpr
            expr = (mkNumber 2 / mkNumber 3) * ((x * (x + mkNumber 1)) / (x + mkNumber 2)) * (y ** n)
            expected = mkNumber 2 * x * (x + mkNumber 1) * (y ** n)
        case numer (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "numer failed: " ++ show e
    ]

denomTests :: TestTree
denomTests =
  testGroup
    "denom"
    [ testCase "denom of (x^2 + 1)/(x + 1) is x + 1" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x ** (2 :: UnsimplifiedExpr) + mkNumber 1) / (x + mkNumber 1)
            expected = x + mkNumber 1
        case denom (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "denom failed: " ++ show e
    , testCase "denom of 1/(x^2 + 1) is x^2 + 1" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = mkNumber 1 / (x ** (2 :: UnsimplifiedExpr) + mkNumber 1)
            expected = x ** (2 :: UnsimplifiedExpr) + mkNumber 1
        case denom (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "denom failed: " ++ show e
    , testCase "denom of (x^3 + x^2 + x + 1)/(x^2 + 1) is x^2 + 1" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x ** (3 :: UnsimplifiedExpr) + x ** (2 :: UnsimplifiedExpr) + x + mkNumber 1) / (x ** (2 :: UnsimplifiedExpr) + mkNumber 1)
            expected = x ** (2 :: UnsimplifiedExpr) + mkNumber 1
        case denom (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "denom failed: " ++ show e
    , testCase "denom of sin(x)/cos(x) is cos(x)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = mkFunction "sin" (x :| []) / mkFunction "cos" (x :| [])
            expected = mkFunction "cos" (x :| [])
        case denom (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "denom failed: " ++ show e
    , testCase "denom of 1/sin(x) is sin(x)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = mkNumber 1 / mkFunction "sin" (x :| [])
            expected = mkFunction "sin" (x :| [])
        case denom (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "denom failed: " ++ show e
    , testCase "numer of (2/3)*((x*(x + 1))/(x + 2))*y^n is 3*(x + 2)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            n = mkSymbol "n" :: UnsimplifiedExpr
            expr = (mkNumber 2 / mkNumber 3) * ((x * (x + mkNumber 1)) / (x + mkNumber 2)) * (y ** n)
            expected = mkNumber 3 * (x + mkNumber 2)
        case denom (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "denom failed: " ++ show e
    ]

rationalGreTests :: TestTree
rationalGreTests =
  testGroup
    "isRationalGre"
    [ testCase "(x^2 + 1)/(2*x + 3) is rational in {x}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x ** (2 :: UnsimplifiedExpr) + mkNumber 1) / (mkNumber 2 * x + mkNumber 3)
        isRationalGre (simplifyOrFail expr) (HS.fromList [simplifyOrFail x]) @?= True
    , testCase "1/x + 1/y is not rational in {x,y}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = mkNumber 1 / x + mkNumber 1 / y
        isRationalGre (simplifyOrFail expr) (HS.fromList [simplifyOrFail x, simplifyOrFail y]) @?= False
    ]

rationalVariablesTests :: TestTree
rationalVariablesTests =
  testGroup
    "rationalVariables"
    [ testCase "Rational_variables((2*x + 3*y)/(z + 4)) -> {x, y, z}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            z = mkSymbol "z" :: UnsimplifiedExpr
            expr = (mkNumber 2 * x + mkNumber 3 * y) / (z + mkNumber 4)
        case rationalVariables (simplifyOrFail expr) of
          Right out -> out @?= HS.fromList [simplifyOrFail x, simplifyOrFail y, simplifyOrFail z]
          Left e -> fail $ "rationalVariables failed: " ++ show e
    , testCase "Rational_variables(1/x + 1/y) -> {1/x, 1/y}" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = mkNumber 1 / x + mkNumber 1 / y
        case rationalVariables (simplifyOrFail expr) of
          Right out ->
            out
              @?= HS.fromList
                [ simplifyOrFail (mkNumber 1 / x)
                , simplifyOrFail (mkNumber 1 / y)
                ]
          Left e -> fail $ "rationalVariables failed: " ++ show e
    ]

rationaliseTests :: TestTree
rationaliseTests =
  testGroup
    "rationalise"
    [ testCase "rationalise((1 + 1/x)^2) -> (x + 1)^2 / x^2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (mkNumber 1 + mkNumber 1 / x) ** (2 :: UnsimplifiedExpr)
            expected = ((x + mkNumber 1) ** (2 :: UnsimplifiedExpr)) / (x ** (2 :: UnsimplifiedExpr))
        case rationalise (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "rationalise failed: " ++ show e
    , testCase "rationalise((1 + 1/x)^(1/2)) -> ((x + 1)/x)^(1/2)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (mkNumber 1 + mkNumber 1 / x) ** mkFraction 1 2
            expected = ((x + mkNumber 1) / x) ** mkFraction 1 2
        case rationalise (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "rationalise failed: " ++ show e
    , testCase "rationalise(1/(1 + 1/x)^(1/2) + (1 + 1/x)^(3/2)) -> (x^2 + (x + 1)^2) / (x^2 * ((x + 1)/x)^(1/2))" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            u = mkNumber 1 + mkNumber 1 / x
            expr = mkNumber 1 / (u ** mkFraction 1 2) + (u ** mkFraction 3 2)
            expected = (x ** (2 :: UnsimplifiedExpr) + (x + mkNumber 1) ** (2 :: UnsimplifiedExpr)) / (x ** (2 :: UnsimplifiedExpr) * (((x + mkNumber 1) / x) ** mkFraction 1 2))
        case rationalise (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "rationalise failed: " ++ show e
    , testCase "rationalise m/r + n/s -> (m*s + n*r) / (r*s)" $ do
        let m = mkSymbol "m" :: UnsimplifiedExpr
            n = mkSymbol "n" :: UnsimplifiedExpr
            r = mkSymbol "r" :: UnsimplifiedExpr
            s = mkSymbol "s" :: UnsimplifiedExpr
            expr = m / r + n / s
            expected = (m * s + n * r) / (r * s)
        case rationalise (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "rationalise failed: " ++ show e
    , testCase "rationalise a/b + c/d + e/f -> (a*d*f + b*(c*f + d*e)) / (b*d*f)" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            c = mkSymbol "c" :: UnsimplifiedExpr
            d = mkSymbol "d" :: UnsimplifiedExpr
            e = mkSymbol "e" :: UnsimplifiedExpr
            f = mkSymbol "f" :: UnsimplifiedExpr
            expr = a / b + c / d + e / f
            expected = (a * d * f + b * (c * f + d * e)) / (b * d * f)
        case rationalise (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e'   -> fail $ "rationalise failed: " ++ show e'
    ]

rationalExpandTests :: TestTree
rationalExpandTests =
  testGroup
    "rationalExpand"
    [ testCase "(sqrt(1 / ((x+y)^2 + 1)) + 1)*(sqrt(1 / ((x+y)^2 + 1)) - 1) / (x + 1) -> (-x^2 -2*x*y - y^2) / (x^3 + x^2 + 2x^2*y + 2*x*y + x*y^2 + y^2 + x + 1)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            innerSqrt = mkNumber 1 / ((x + y) ** 2 + mkNumber 1)
            expr = (sqrt innerSqrt + 1) * (sqrt innerSqrt - 1) / (x + 1)
            expected =
              ( -(x ** 2)
                  - 2 * x * y
                  - y ** 2
              )
                / ( x ** 3
                      + x ** 2
                      + 2 * x ** 2 * y
                      + 2 * x * y
                      + x * y ** 2
                      + y ** 2
                      + x
                      + 1
                  )
        case rationalExpand (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "rationalExpand failed: " ++ show e
    , testCase "1/(1/a + c/(a*b)) + ((a*b*c + a*c^2) / (b + c)^2) - a -> 0" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            c = mkSymbol "c" :: UnsimplifiedExpr
            expr = 1 / (1 / a + c / (a * b)) + (a * b * c + a * c ** 2) / (b + c) ** 2 - a
            expected = 0
        case rationalExpand (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "rationalExpand failed: " ++ show e
    ]

expandMainOpTests :: TestTree
expandMainOpTests =
  testGroup
    "expandMainOp"
    [ testCase "numbers pass through unchanged" $ do
        let expr = mkNumber 7 :: UnsimplifiedExpr
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expr
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "symbols pass through unchanged" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
        case expandMainOp (simplifyOrFail x) of
          Right out -> out @?= simplifyOrFail x
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "sums pass through unchanged" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = 2 + x + (x ** 2)
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expr
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "x * (2 + (1 + x)^2) expands only the top-level product" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = x * (2 + ((1 + x) ** 2))
            expected = 2 * x + x * ((1 + x) ** 2)
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "(2 + (1 + x)^2) * x expands the right-hand product branch" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (2 + ((1 + x) ** 2)) * x
            expected = 2 * x + ((1 + x) ** 2) * x
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "x^2 passes through unchanged" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = x ** 2
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expr
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "(x + y)^2 expands only the outer power" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = (x + y) ** 2
            expected = x ** 2 + 2 * x * y + y ** 2
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "(x + y)^(3/2) keeps the fractional part intact" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = (x + y) ** mkFraction 3 2
            expected = ((x + y) ** mkFraction 1 2) * (x + y)
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "(x*(y + 1)^(3/2) + 1)*(x*(y + 1)^(3/2) - 1) expands to x^2*(y + 1)^3 - 1" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            term = x * (y + 1) ** mkFraction 3 2
            expr = (term + 1) * (term - 1)
            expected = x ** 2 * (y + 1) ** 3 - 1
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "(x + 2)*(x + 3)*(x + 4) expands to x^3 + 9*x^2 + 26*x + 24" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x + 2) * (x + 3) * (x + 4)
            expected = x ** 3 + 9 * x ** 2 + 26 * x + 24
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "a / ((x + 1)*(x + 2)) expands to a / ((x + 1)*(x + 2))" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            expr = a / ((x + 1) * (x + 2))
            expected = a / ((x + 1) * (x + 2))
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "sin(a*(b + c)) expands to sin(a*(b + c))" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            c = mkSymbol "c" :: UnsimplifiedExpr
            expr = mkFunction "sin" (a * (b + c) :| [])
            expected = mkFunction "sin" (a * (b + c) :| [])
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "((x + 2)^2)^2 expands to x^4 + 8*x^3 + 24*x^2 + 32*x + 16" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = ((x + 2) ** 2) ** 2
            expected = x ** 4 + 8 * x ** 3 + 24 * x ** 2 + 32 * x + 16
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "(x + (1 + x)^2)^2 expands to x^2 + 2*x*(1 + x)^2 + (1 + x)^4" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (x + (1 + x) ** 2) ** 2
            expected = x ** 2 + 2 * x * (1 + x) ** 2 + (1 + x) ** 4
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    , testCase "2*x expands to 2*x" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = 2 * x
            expected = 2 * x
        case expandMainOp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e    -> fail $ "expandMainOp failed: " ++ show e
    ]
