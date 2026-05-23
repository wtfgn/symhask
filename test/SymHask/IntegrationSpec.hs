{-# LANGUAGE ScopedTypeVariables #-}

module SymHask.IntegrationSpec
    ( tests
    ) where

import qualified Data.HashSet                          as HS
import           SymHask.Symbolic                      (UnsimplifiedExpr,
                                                        mkSymbol)
import           SymHask.Symbolic.Calculus.Integration (integrate,
                                                        integrateLinear,
                                                        integrateTable,
                                                        trialSubstitutions)
import           Test.Tasty                            (TestTree, testGroup)
import           Test.Tasty.HUnit                      (testCase, (@?=))
import           TestUtils                             (simplifyOrFail)

tests :: TestTree
tests =
  testGroup
    "Integration"
    [ integrationTableTests
    , linearPropertiesTests
    , integrateTests
    , trialSubTests
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
          runTable e = integrateTable "x" (simplifyOrFail e)
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
          runLinear e = integrateLinear "x" (simplifyOrFail e)
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
          runIntegrate e = integrate "x" (simplifyOrFail e)
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

-- ============================================================================
-- Trial Substitutions
-- ============================================================================

trialSubTests :: TestTree
trialSubTests =
    testGroup
        "trialSubstitutions"
        [ let x = mkSymbol "x" :: UnsimplifiedExpr
              run e = trialSubstitutions (simplifyOrFail e)
           in testGroup
                "candidates"
                [ testCase "sin(x) yields sin(x) and x" $
                    let s = run (sin x)
                     in (HS.member (simplifyOrFail (sin x)) s @?= True) >> (HS.member (simplifyOrFail x) s @?= True)
                , testCase "x^2 yields base x and exponent 2" $
                    let s = run (x ** (2 :: UnsimplifiedExpr))
                     in (HS.member (simplifyOrFail x) s @?= True) >> (HS.member (simplifyOrFail (2 :: UnsimplifiedExpr)) s @?= True)
                , testCase "(sin x)^2 yields sin(x) and x and 2" $
                    let s = run (sin x ** (2 :: UnsimplifiedExpr))
                     in (HS.member (simplifyOrFail (sin x)) s @?= True) >> (HS.member (simplifyOrFail x) s @?= True) >> (HS.member (simplifyOrFail (2 :: UnsimplifiedExpr)) s @?= True)
                , testCase "complex integrand: (x+1)*ln(cos((x+1)^2))*sin((x+1)^2) / (cos((x+1)^2))" $
                    let xPlus1 = x + 1
                        innerPower = xPlus1 ** (2 :: UnsimplifiedExpr)
                        cosInner = cos innerPower
                        logCos = log cosInner
                        sinCos = sin cosInner
                        expr = xPlus1 * logCos * sinCos / cosInner
                        s = run expr
                     in do
                            HS.member (simplifyOrFail logCos) s @?= True
                            HS.member (simplifyOrFail cosInner) s @?= True
                            HS.member (simplifyOrFail innerPower) s @?= True
                            HS.member (simplifyOrFail xPlus1) s @?= True
                            HS.member (simplifyOrFail sinCos) s @?= True
                            HS.member (simplifyOrFail (-1 :: UnsimplifiedExpr)) s @?= True
                            HS.member (simplifyOrFail (2 :: UnsimplifiedExpr)) s @?= True
                ]
        ]
