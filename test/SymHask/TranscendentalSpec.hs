{-# LANGUAGE ScopedTypeVariables #-}

module SymHask.TranscendentalSpec
  ( tests,
  )
where

import SymHask.Symbolic
import SymHask.Symbolic.Transcendental (contractExp, expandExp, expandTrig, separateSinCos, trigSubs, contractTrig)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import TestUtils (simplifyOrFail)

tests :: TestTree
tests = testGroup "Transcendental"
  [ expandExpTests
  , expandTrigTests
  , contractExpTests
  , contractTrigTests
  , separateSinCosTests
  , expandTrigSubsTests
  ]

contractExpTests :: TestTree
contractExpTests =
  testGroup
    "contractExp"
    [ testCase "exp(x) * exp(y) contracts to exp(x + y)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = exp x * exp y
            expected = exp (x + y)
        case contractExp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractExp failed: " ++ show e,
      testCase "x * y stays x * y" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = x * y
        case contractExp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expr
          Left e -> fail $ "contractExp failed: " ++ show e,
      testCase "exp(x)^2 contracts to exp(2*x)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = exp x ** 2
            expected = exp (2 * x)
        case contractExp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractExp failed: " ++ show e,
      testCase "exp(x) * a * exp(y) contracts to a * exp(x + y)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            a = mkSymbol "a" :: UnsimplifiedExpr
            expr = exp x * a * exp y
            expected = a * exp (x + y)
        case contractExp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractExp failed: " ++ show e,
      testCase "exp(x)*(exp(x) + exp(y)) contracts tp exp(2*x) + exp(x + y)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = exp x * (exp x + exp y)
            expected = exp (2 * x) + exp (x + y)
        case contractExp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractExp failed: " ++ show e,
      testCase "exp(exp(x))^exp(y) contracts to exp(exp(x + y))" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = exp (exp x) ** exp y
            expected = exp (exp (x + y))
        case contractExp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractExp failed: " ++ show e
    ]

contractTrigTests :: TestTree
contractTrigTests =
  testGroup
    "contractTrig"
    [ testCase "sin(x)*sin(y) contracts to cos(x-y)/2 - cos(x+y)/2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = sin x * sin y
            expected = cos (x - y) / 2 - cos (x + y) / 2
        case contractTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractTrig failed: " ++ show e,
      testCase "cos(x)*cos(y) contracts to cos(x+y)/2 + cos(x-y)/2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = cos x * cos y
            expected = cos (x + y) / 2 + cos (x - y) / 2
        case contractTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractTrig failed: " ++ show e,
      testCase "sin(x)*cos(y) contracts to sin(x+y)/2 + sin(x-y)/2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = sin x * cos y
            expected = sin (x + y) / 2 + sin (x - y) / 2
        case contractTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractTrig failed: " ++ show e,
      testCase "cos(x)*sin(y) contracts to sin(x+y)/2 + sin(y-x)/2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = cos x * sin y
            expected = sin (x + y) / 2 + sin (y - x) / 2
        case contractTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractTrig failed: " ++ show e,
      testCase "a*sin(x)*sin(y) contracts with non-trig factor" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            a = mkSymbol "a" :: UnsimplifiedExpr
            expr = a * sin x * sin y
        case contractTrig (simplifyOrFail expr) of
          Right _ -> return ()
          Left e -> fail $ "contractTrig failed: " ++ show e,
      testCase "sin(x) stays sin(x)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = sin x
        case contractTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expr
          Left e -> fail $ "contractTrig failed: " ++ show e,
      testCase "3 stays 3" $ do
        let expr = (3 :: UnsimplifiedExpr)
        case contractTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expr
          Left e -> fail $ "contractTrig failed: " ++ show e,
      testCase "cos(x)^4 contracts to (1/8)*cos(4*x) + (1/2)*cos(2*x) + 3/8" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = cos x ** 4
            expected = (1 / 8) * cos (4 * x) + (1 / 2) * cos (2 * x) + (3 / 8)
        case contractTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractTrig failed: " ++ show e,
      testCase "sin(x)^2 contracts to 1/2 - cos(2x)/2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = sin x ** 2
            expected = (1 / 2) - (cos (2 * x) / 2)
        case contractTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractTrig failed: " ++ show e,
      testCase "cos(x)^2 contracts to 1/2 + cos(2x)/2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = cos x ** 2
            expected = (1 / 2) + (cos (2 * x) / 2)
        case contractTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractTrig failed: " ++ show e,
      testCase "cos(2*x)^2 contracts to 1/2 + cos(4*x)/2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = cos (2 * x) ** 2
            expected = (1 / 2) + (cos (4 * x) / 2)
        case contractTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractTrig failed: " ++ show e,
      testCase "sin(x)^2 * cos(x)^2 contracts to (1/8)-(cos(4*x)/8)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = (sin x ** 2) * (cos x ** 2)
            expected = (1 / 8) - (cos (4 * x) / 8)
        case contractTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractTrig failed: " ++ show e,
      testCase "(sin(x) + cos(y)) * cos(y) contracts tp som(x + y)/2 + sin(x - y)/2 + 1/2 + cos(2*y)/2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = (sin x + cos y) * cos y
            expected = sin (x + y) / 2 + sin (x - y) / 2 + (1 / 2) + (cos (2 * y) / 2)
        case contractTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "contractTrig failed: " ++ show e
    ]

separateSinCosTests :: TestTree
separateSinCosTests =
  testGroup
    "separateSinCos"
    [ testCase "separateSinCos(3*sin(x)*cos(y)) -> (3, sin(x)*cos(y))" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = 3 * sin x * cos y
            expected = (simplifyOrFail (3 :: UnsimplifiedExpr), simplifyOrFail (sin x * cos y))
        case separateSinCos (simplifyOrFail expr) of
          Right out -> out @?= expected
          Left e -> fail $ "separateSinCos failed: " ++ show e,
      testCase "separateSinCos(1 + sin(x)) -> (1 + sin(x), 1)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = 1 + sin x
            expected = (simplifyOrFail expr, simplifyOrFail (1 :: UnsimplifiedExpr))
        case separateSinCos (simplifyOrFail expr) of
          Right out -> out @?= expected
          Left e -> fail $ "separateSinCos failed: " ++ show e,
      testCase "separateSinCos(sin(x)) -> (1, sin(x))" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = sin x
            expected = (simplifyOrFail (1 :: UnsimplifiedExpr), simplifyOrFail expr)
        case separateSinCos (simplifyOrFail expr) of
          Right out -> out @?= expected
          Left e -> fail $ "separateSinCos failed: " ++ show e,
      testCase "separateSinCos(cos(x)^2) -> (1, cos(x)^2)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = cos x ** 2
            expected = (simplifyOrFail (1 :: UnsimplifiedExpr), simplifyOrFail expr)
        case separateSinCos (simplifyOrFail expr) of
          Right out -> out @?= expected
          Left e -> fail $ "separateSinCos failed: " ++ show e,
      testCase "separateSinCos(x*sin(y)^2*cos(y)*z^3) -> (x*z^3, sin(y)^2*cos(y))" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            z = mkSymbol "z" :: UnsimplifiedExpr
            expr = x * (sin y ** 2) * cos y * (z ** 3)
            expected = (simplifyOrFail (x * (z ** 3)), simplifyOrFail ((sin y ** 2) * cos y))
        case separateSinCos (simplifyOrFail expr) of
          Right out -> out @?= expected
          Left e -> fail $ "separateSinCos failed: " ++ show e
    ]

expandExpTests :: TestTree
expandExpTests =
  testGroup
    "expandExp"
    [ testCase "exp(a*(b + c)) expands to exp(a*b) * exp(a*c)" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            c = mkSymbol "c" :: UnsimplifiedExpr
            expr = exp (a * (b + c))
            expected = exp (a * b) * exp (a * c)
        case expandExp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "expandExp failed: " ++ show e,
      testCase "exp(2*x) expands to exp(x)^2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = exp (2 * x)
            expected = exp x ** 2
        case expandExp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "expandExp failed: " ++ show e,
      testCase "exp((x+y)*(x-y)) expands to exp(x^2) / exp(y^2)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = exp ((x + y) * (x - y))
            expected = exp (x ** 2) / exp (y ** 2)
        case expandExp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "expandExp failed: " ++ show e,
      testCase "exp(2*w*x + 3*y*z) expands to exp(w*x)^2 * exp(y*z)^3" $ do
        let w = mkSymbol "w" :: UnsimplifiedExpr
            x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            z = mkSymbol "z" :: UnsimplifiedExpr
            expr = exp (2 * w * x + 3 * y * z)
            expected = exp (w * x) ** 2 * exp (y * z) ** 3
        case expandExp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "expandExp failed: " ++ show e,
      testCase "exp(2*(x + y)) expands to exp(x)^2 * exp(y)^2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = exp (2 * (x + y))
            expected = exp x ** 2 * exp y ** 2
        case expandExp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "expandExp failed: " ++ show e,
      testCase "exp((x + y)*(x - y)) expands to exp(x^2) / exp(y^2)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = exp ((x + y) * (x - y))
            expected = exp (x ** 2) / exp (y ** 2)
        case expandExp (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "expandExp failed: " ++ show e,
      testCase "1 / (exp(2*x) - exp(x)^2) returns DivisionByZero" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = 1 / (exp (mkNumber 2 * x) - exp x ** 2)
        case expandExp (simplifyOrFail expr) of
          Left DivisionByZero -> pure ()
          Left e -> fail $ "Expected DivisionByZero, got: " ++ show e
          Right out -> fail $ "Expected DivisionByZero, got: " ++ show (out :: SimplifiedExpr)
    ]

expandTrigSubsTests :: TestTree
expandTrigSubsTests =
  testGroup
    "trigSubs"
    [ testCase "tan(x) -> sin(x)/cos(x)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = tan x
            expected = sin x / cos x
        case trigSubs (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "trigSubs failed: " ++ show e,
      testCase "cot(x) -> cos(x)/sin(x)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = Cot' x
            expected = cos x / sin x
        case trigSubs (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "trigSubs failed: " ++ show e,
      testCase "sec(x) -> 1/cos(x)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = Sec' x
            expected = 1 / cos x
        case trigSubs (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "trigSubs failed: " ++ show e,
      testCase "csc(x) -> 1/sin(x)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = Csc' x
            expected = 1 / sin x
        case trigSubs (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "trigSubs failed: " ++ show e,
      testCase "csc(x) + cot(y) / (tan(x) - x) -> 1/sin(x) + cos(y)/sin(y) / (sin(x)/cos(x) - x)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = Csc' x + Cot' y / (Tan' x - x)
            expected = 1 / sin x + cos y / sin y / (sin x / cos x - x)
        case trigSubs (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "trigSubs failed: " ++ show e
    ]

expandTrigTests :: TestTree
expandTrigTests =
  testGroup
    "expandTrig"
    [ testCase "sin(a + b) expands using the sum identity" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            expr = sin (a + b)
            expected = sin a * cos b + cos a * sin b
        case expandTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "expandTrig failed: " ++ show e,
      testCase "cos(a + b) expands using the sum identity" $ do
        let a = mkSymbol "a" :: UnsimplifiedExpr
            b = mkSymbol "b" :: UnsimplifiedExpr
            expr = cos (a + b)
            expected = cos a * cos b - sin a * sin b
        case expandTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "expandTrig failed: " ++ show e,
      testCase "sin(2*x) expands using the multiple-angle rule" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = sin (2 * x)
            expected = 2 * sin x * cos x
        case expandTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "expandTrig failed: " ++ show e,
      testCase "sin(-x) expands to -sin(x)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            expr = sin (-x)
            expected = -sin x
        case expandTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "expandTrig failed: " ++ show e,
      testCase "sin(2*x + 3*y) expands to sin(x)^2*sin(y)^3 + 2*sin(x)*cos(x)*cos(y)^3 -cos(x)^2*sin(y)^3 - 3*sin(x)^2*sin(y)*cos(y)^2 + 3*cos(x)^2*sin(y)^2*cos(y)^2 - 6*cos(x)*sin(x)*cos(y)*sin(y)^2" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = sin (2 * x + 3 * y)
            expected
              = sin x ** 2 * sin y ** 3
              + 2 * sin x * cos x * cos y ** 3
              - cos x ** 2 * sin y ** 3
              - 3 * sin x ** 2 * sin y * cos y ** 2
              + 3 * cos x ** 2 * sin y * cos y ** 2
              - 6 * cos x * sin x * cos y * sin y ** 2
        case expandTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "expandTrig failed: " ++ show e,
      testCase "sin(2*(x + y)) expands to 2 cos^2(x) sin(y) cos(y) + 2 sin(x) cos(x) cos^2(y) - 2 sin(x) cos(x) sin^2(y) - 2 sin^2(x) sin(y) cos(y)" $ do
        let x = mkSymbol "x" :: UnsimplifiedExpr
            y = mkSymbol "y" :: UnsimplifiedExpr
            expr = sin (2 * (x + y))
            expected
              = 2 * cos x ** 2 * sin y * cos y
              + 2 * sin x * cos x * cos y ** 2
              - 2 * sin x * cos x * sin y ** 2
              - 2 * sin x ** 2 * sin y * cos y
        case expandTrig (simplifyOrFail expr) of
          Right out -> out @?= simplifyOrFail expected
          Left e -> fail $ "expandTrig failed: " ++ show e,
        testCase "cos(5*x) expands to cos(x)^5 - 10*cos(x)^3*sin(x)^2 + 5*cos(x)*sin(x)^4" $ do
          let x = mkSymbol "x" :: UnsimplifiedExpr
              expr = cos (5 * x)
              expected = cos x ** 5 - 10 * cos x ** 3 * sin x ** 2 + 5 * cos x * sin x ** 4
          case expandTrig (simplifyOrFail expr) of
            Right out -> out @?= simplifyOrFail expected
            Left e -> fail $ "expandTrig failed: " ++ show e,
        testCase "sin(x - 2*y) expands to -sin(x)*sin^2(y) + sin(x)*cos(y)^2 - 2*cos(x)*sin(y)*cos(y)" $ do
          let x = mkSymbol "x" :: UnsimplifiedExpr
              y = mkSymbol "y" :: UnsimplifiedExpr
              expr = sin (x - 2 * y)
              expected = - (sin x * sin y ** 2) + sin x * cos y ** 2 - 2 * cos x * sin y * cos y
          case expandTrig (simplifyOrFail expr) of
            Right out -> out @?= simplifyOrFail expected
            Left e -> fail $ "expandTrig failed: " ++ show e,
        testCase "sin((x+y)^2) expands to sin(x^2) cos(y^2) cos^2(x y) + cos(x^2) sin(y^2) cos^2(x y) - sin(x^2) cos(y^2) sin^2(x y) - cos(x^2) sin(y^2) sin^2(x y) + 2 cos(x^2) cos(y^2) sin(x y) cos(x y) - 2 sin(x^2) sin(y^2) sin(x y) cos(x y)" $ do
          let x = mkSymbol "x" :: UnsimplifiedExpr
              y = mkSymbol "y" :: UnsimplifiedExpr
              expr = sin ((x + y) ** 2)
              expected
                = sin (x ** 2) * cos (y ** 2) * cos (x * y) ** 2
                + cos (x ** 2) * sin (y ** 2) * cos (x * y) ** 2
                - sin (x ** 2) * cos (y ** 2) * sin (x * y) ** 2
                - cos (x ** 2) * sin (y ** 2) * sin (x * y) ** 2
                + 2 * cos (x ** 2) * cos (y ** 2) * sin (x * y) * cos (x * y)
                - 2 * sin (x ** 2) * sin (y ** 2) * sin (x * y) * cos (x * y)
          case expandTrig (simplifyOrFail expr) of
            Right out -> out @?= simplifyOrFail expected
            Left e -> fail $ "expandTrig failed: " ++ show e,
        testCase "1 / (sin(2*x) - 2*sin(x)*cos(x)) returns DivisionByZero" $ do
          let x = mkSymbol "x" :: UnsimplifiedExpr
              expr = 1 / (sin (2 * x) - 2 * sin x * cos x)
          case expandTrig (simplifyOrFail expr) of
            Left DivisionByZero -> pure ()
            Left e -> fail $ "Expected DivisionByZero, got: " ++ show e
            Right out -> fail $ "Expected DivisionByZero, got: " ++ show (out :: SimplifiedExpr)
    ]
