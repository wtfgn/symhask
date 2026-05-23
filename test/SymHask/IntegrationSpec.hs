{-# LANGUAGE ScopedTypeVariables #-}

module SymHask.IntegrationSpec
    ( tests
    ) where

import           Data.List.NonEmpty                    (NonEmpty ((:|)))
import           SymHask.Symbolic                      (UnsimplifiedExpr,
                                                        mkSymbol)
import           SymHask.Symbolic.Calculus.Integration (integrate,
                                                        integrateLinear,
                                                        integrateTable,
                                                        mkIntegrationVar)
import           Test.Tasty                            (TestTree, testGroup)
import           Test.Tasty.HUnit                      (assertFailure, testCase,
                                                        (@?=))
import           TestUtils                             (simplifyOrFail)

tests :: TestTree
tests =
  testGroup
    "Integration"
    [ integrationTableTests
    , linearPropertiesTests
    , integrateTests
    ]

-- ============================================================================

-- * Integration Table Tests

-- ============================================================================

integrationTableTests :: TestTree
integrationTableTests :: TestTree =
  testGroup
    "Integration Table"
    [ -- Category 1: Constants (free of integration variable)
      let x = mkSymbol "x" :: UnsimplifiedExpr
          mkI = either (\_ -> error "mkIntegrationVar failed") id . mkIntegrationVar
          runTable e = integrateTable (mkI x) (simplifyOrFail e)
       in testGroup
            "table"
            [ testCase "Constant: ∫ 5 dx = 5x" $ runTable (5 :: UnsimplifiedExpr) @?= Just (simplifyOrFail (5 * x))
            , testCase "Power rule: ∫ x^2 dx = x^3/3" $ runTable (x ** 2) @?= Just (simplifyOrFail ((x ** 3) / 3))
            , testCase "Power log: ∫ x^(-1) dx = ln(x)" $ runTable (x ** (-1)) @?= Just (simplifyOrFail (log x))
            , testCase "Exponential: ∫ exp(x) dx = exp(x)" $ runTable (exp x) @?= Just (simplifyOrFail (exp x))
            , testCase "Sine: ∫ sin(x) dx = -cos(x)" $ runTable (sin x) @?= Just (simplifyOrFail (-cos x))
            , testCase "Cosine: ∫ cos(x) dx = sin(x)" $ runTable (cos x) @?= Just (simplifyOrFail (sin x))
            , testCase "No match: ∫ x^x dx returns Nothing" $ runTable (x ** x) @?= Nothing
            ]
    ]

-- ============================================================================

-- * Linear Properties Tests

-- ============================================================================

linearPropertiesTests :: TestTree
linearPropertiesTests =
  testGroup
    "Linear Properties"
    [ let x = mkSymbol "x" :: UnsimplifiedExpr
          mkI = either (\_ -> error "mkIntegrationVar failed") id . mkIntegrationVar
          runLinear e = integrateLinear (mkI x) (simplifyOrFail e)
       in testGroup
            "linear"
            [ testCase "Product constant: ∫ 5*x^2 = 5*(x^3/3)" $ runLinear (5 * (x ** 2)) @?= Just (simplifyOrFail (5 * ((x ** 3) / 3)))
            , testCase "Product pi*sin: ∫ π*sin(x) = -π*cos(x)" $ runLinear (mkSymbol "pi" * sin x) @?= Just (simplifyOrFail (mkSymbol "pi" * (-cos x)))
            , testCase "Sum: ∫ (x + x^2) = x^2/2 + x^3/3" $ runLinear (x + x ** 2) @?= Just (simplifyOrFail ((x ** 2) / 2 + (x ** 3) / 3))
            , testCase "Sum mixed: ∫ (x + 2*sin(x) + 5)" $ runLinear (x + 2 * sin x + 5) @?= Just (simplifyOrFail ((x ** 2) / 2 + 2 * (-cos x) + 5 * x))
            , testCase "Dependent product: ∫ x*sin(x) = Nothing" $ runLinear (x * sin x) @?= Nothing
            , testCase "Non-product/sum: ∫ exp(x) = Nothing" $ runLinear (exp x) @?= Nothing
            ]
    ]

-- ============================================================================

-- * Integration Tests

-- ============================================================================
integrateTests :: TestTree
integrateTests =
  testGroup
    "Integration"
    [ let x = mkSymbol "x" :: UnsimplifiedExpr
          mkI = either (\_ -> error "mkIntegrationVar failed") id . mkIntegrationVar
          runIntegrate e = integrate (mkI x) (simplifyOrFail e)
       in testGroup
            "integrate"
            [ testCase "∫ (x+1)*ln(cos((x+1)^2))*sin((x+1)^2)/cos((x+1)^2)" $
                let xPlus1 = x + 1
                    inner = xPlus1 ** 2
                    integrand = xPlus1 * log (cos inner) * sin inner / cos inner
                    expected = -((log (cos inner) ** 2) / 4)
                 in runIntegrate integrand @?= Just (simplifyOrFail expected)
            , testCase "∫ (x+1)*exp((x+1)^2)" $
                let xPlus1 = x + 1
                    inner = xPlus1 ** 2
                    integrand = xPlus1 * exp inner
                    expected = exp inner / 2
                 in runIntegrate integrand @?= Just (simplifyOrFail expected)
            , testCase "∫ sin(x)*cos(x)" $
                let integrand = sin x * cos x
                    expected = -((cos x ** 2) / 2)
                 in runIntegrate integrand @?= Just (simplifyOrFail expected)
            , testCase "∫ 2*x*cos(x^2)" $
                let inner = x ** 2
                    integrand = 2 * x * cos inner
                    expected = sin inner
                 in runIntegrate integrand @?= Just (simplifyOrFail expected)
            , testCase "∫ 2*x*(x^2 +4)^5" $
                let inner = x ** 2 + 4
                    integrand = 2 * x * (inner ** 5)
                    expected = (inner ** 6) / 6
                 in runIntegrate integrand @?= Just (simplifyOrFail expected)
            , testCase "∫ cos(x)*2^sin(x)" $
                let integrand = cos x * (2 ** sin x)
                    expected = (2 ** sin x) / log 2
                 in runIntegrate integrand @?= Just (simplifyOrFail expected)
            ]
    ]
