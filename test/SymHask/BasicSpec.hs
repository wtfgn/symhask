{-# LANGUAGE ScopedTypeVariables #-}

module SymHask.BasicSpec
    ( tests
    ) where

import qualified Data.HashSet           as HS
import           SymHask.Symbolic       (UnsimplifiedExpr, mkSymbol)
import           SymHask.Symbolic.Basic (trialSubstitutions)
import           Test.Tasty             (TestTree, testGroup)
import           Test.Tasty.HUnit       (testCase, (@?=))
import           TestUtils              (simplifyOrFail)

tests :: TestTree
tests =
    testGroup
        "Basic"
        [ trialSubTests
        ]

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
