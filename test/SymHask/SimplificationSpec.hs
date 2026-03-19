{-# LANGUAGE ScopedTypeVariables #-}
module SymHask.SimplificationSpec
    ( tests
    ) where

import           Data.List.NonEmpty                                      (NonEmpty ((:|)))
import           SymHask.Symbolic                                        (UnsimplifiedExpr,
                                                                          mkFraction,
                                                                          mkFunction,
                                                                          mkNumber,
                                                                          mkSum,
                                                                          mkSymbol)
import           SymHask.Symbolic.Simplification.AutomaticSimplification (automaticSimplify)
import           Test.Tasty                                              (TestTree,
                                                                          testGroup)
import           Test.Tasty.HUnit                                        (testCase,
                                                                          (@?),
                                                                          (@?=))
import           Test.Tasty.QuickCheck                                   (forAll,
                                                                          suchThat,
                                                                          testProperty)
import           TestUtils                                               (valInteger, fractionExpr, integerExpr)

tests :: TestTree
tests = testGroup "Simplification"
  [ unitTests
  , integrationTests
  , propertyTests
  ]

-- ============================================================================
-- 1. Unit Tests (Deterministic verification of specific rules)
-- ============================================================================
unitTests :: TestTree
unitTests = testGroup "Unit Tests"
  [ testCase "Addition Identity: x + 0 -> x" $ do
      let x :: UnsimplifiedExpr = mkSymbol "x"
          expr = x + 0
      automaticSimplify expr @?= Right x

  , testCase "Multiplication Identity: x * 1 -> x" $ do
      let x :: UnsimplifiedExpr = mkSymbol "x"
          expr = x * 1
      automaticSimplify expr @?= Right x

  , testCase "Constant Folding: 2 + 3 -> 5" $ do
      let expr :: UnsimplifiedExpr = 2 + 3
      automaticSimplify expr @?= Right 5

  , testCase "Zero Property: x * 0 -> 0" $ do
      let x :: UnsimplifiedExpr = mkSymbol "x"
          expr = x * 0
      automaticSimplify expr @?= Right 0

  , distributiveUnitTests
  ]

-- The basic distributive transformation in automatic simplification
-- refers to the collection of integer and fraction coefficients of like terms in a sum.
distributiveUnitTests :: TestTree
distributiveUnitTests = testGroup "Distributive Unit Tests"
  [ testCase "Collecting Integer Coefficients: 4*x + 5*x -> (4 + 5)*x" $ do
      let x = mkSymbol "x"
          expr = 4*x + 5*x :: UnsimplifiedExpr
      automaticSimplify expr @?= Right (9*x)

  , testCase "Collecting Fraction Coefficients: (1/2)*x + (1/3)*x -> (1/2 + 1/3)*x" $ do
      let x = mkSymbol "x"
          expr = (mkFraction 1 2)*x + (mkFraction 1 3)*x :: UnsimplifiedExpr
      automaticSimplify expr @?= Right ((mkFraction 5 6)*x)

  , testCase "Mixed Coefficients: 2*x + (1/3)*x -> (2 + 1/3)*x" $ do
      let x = mkSymbol "x"
          expr = 2*x + (mkFraction 1 3)*x :: UnsimplifiedExpr
      automaticSimplify expr @?= Right ((mkFraction 7 3)*x)

    -- This test checks that the system cannot handle ambiguous distribution
    -- of non-constant coefficients, which is a known limitation.
    -- e.g. a*x + b*x + b*y should not simplify to (a + b)*x + b*y or a*x + b*(x + y) because
    -- The system should not attempt to factor out 'b' from both terms because
    -- it cannot determine if 'b' is a constant or a variable, leading to ambiguity
  , testCase "Ambiguous Distribution: a*x + b*x + b*y should not factor out 'b'" $ do
      let a = mkSymbol "a" :: UnsimplifiedExpr
          b = mkSymbol "b" :: UnsimplifiedExpr
          x = mkSymbol "x" :: UnsimplifiedExpr
          y = mkSymbol "y" :: UnsimplifiedExpr
          expr = a*x + b*x + b*y :: UnsimplifiedExpr
      automaticSimplify expr @?= Right (mkSum (a*x :| [b*x, b*y]))

    -- This test checks that the system cannot distribute constants over sums
    -- e.g. x + 1 + (-1)*(x + 1) should not simplify to 0
  , testCase "No Distribution of Constants: x + 1 + (-1)*(x + 1) should not simplify to 0" $ do
      let x = mkSymbol "x" :: UnsimplifiedExpr
          expr = x + 1 + (-1)*(x + 1) :: UnsimplifiedExpr
      automaticSimplify expr @?= Right (mkSum (1 :| [x, mkNumber (-1)*(1 + x)])) -- order applies
  ]

-- ============================================================================
-- 2. Property Tests (Randomized verification of algebraic laws)
-- ============================================================================
propertyTests :: TestTree
propertyTests = testGroup "Algebraic Properties"
  [ distributiveProps
  , associativeProps
  , commutativeProps
  , idempotenceProps
  ]

distributiveProps :: TestTree
distributiveProps = testGroup "Coefficient Collection Properties"
  [ -- 1. Integer Coefficients: a*x + b*x == (a+b)*x
    testProperty "Integer Collection: a*x + b*x -> (a+b)*x" $
      \(x :: UnsimplifiedExpr) ->
        -- Check a and b are not 1 to avoid flattening '1*Sum' into 'Sum'
        forAll (integerExpr `suchThat` (\n -> n /= mkNumber 1)) $ \a ->
        forAll (integerExpr `suchThat` (\n -> n /= mkNumber 1))  $ \b ->
          let term1 = a * x
              term2 = b * x
              expected = (a + b) * x

              -- simplify (a*x + b*x) and expect it to equal (a+b)*x
              result = automaticSimplify (term1 + term2)
              target = automaticSimplify expected

          in result == target

  , -- 2. Rational Coefficients: (n1/d1)*x + (n2/d2)*x == (n1/d1 + n2/d2)*x
    testProperty "Fraction Collection: q1*x + q2*x -> (q1+q2)*x (excluding 1)" $
      \(x :: UnsimplifiedExpr) ->
        -- Filter out fractions that simplify to 1 (e.g. 2/2, 5/5)
        -- This prevents 1*x -> x, which breaks the 'Product' structure expected by the test
        -- (When a coefficient is 1, the expression 1 * x simplifies to just x. 
        -- If x is a Sum, the Associative Law flattens it into the parent expression,
        -- breaking the "like term" structure coeff * term that the simplifier looks for.)
        let isNotOne q = automaticSimplify q /= Right (mkNumber 1)
        in forAll (fractionExpr `suchThat` isNotOne) $ \q1 ->
           forAll (fractionExpr `suchThat` isNotOne) $ \q2 ->
          let term1 = q1 * x
              term2 = q2 * x

              -- Construct expected result using implicit rational arithmetic
              result = automaticSimplify (term1 + term2)
              target = automaticSimplify ((q1 + q2) * x)
          in result == target
  ]

associativeProps :: TestTree
associativeProps = testGroup "Associative Properties"
  [ testProperty "Associativity of Sum: (a + b) + c == a + (b + c)" $
      \(a :: UnsimplifiedExpr) (b :: UnsimplifiedExpr) (c :: UnsimplifiedExpr) ->
        let left  = automaticSimplify ((a + b) + c)
            right = automaticSimplify (a + (b + c))
        in left == right

  , testProperty "Associativity of Product: (a * b) * c == a * (b * c)" $
      \(a :: UnsimplifiedExpr) (b :: UnsimplifiedExpr) (c :: UnsimplifiedExpr) ->
        let left  = automaticSimplify ((a * b) * c)
            right = automaticSimplify (a * (b * c))
        in left == right
  ]

commutativeProps :: TestTree
commutativeProps = testGroup "Commutative Properties"
  [ testProperty "Commutativity of Sum: a + b == b + a" $
      \(a :: UnsimplifiedExpr) (b :: UnsimplifiedExpr) ->
        let left  = automaticSimplify (a + b)
            right = automaticSimplify (b + a)
        in left == right

  , testProperty "Commutativity of Product: a * b == b * a" $
      \(a :: UnsimplifiedExpr) (b :: UnsimplifiedExpr) ->
        let left  = automaticSimplify (a * b)
            right = automaticSimplify (b * a)
        in left == right
  ]

idempotenceProps :: TestTree
idempotenceProps = testGroup "Idempotence Properties"
  [ testProperty "Idempotence: simplify(x) == simplify(simplify(x))" $
      \(x :: UnsimplifiedExpr) ->
        let res1 = automaticSimplify x
        in case res1 of
            Right s -> automaticSimplify s == Right s
            Left _  -> True -- Discard errors generated by random inputs
  ]

-- ============================================================================
-- 3. Integration Tests & Known Limitations
--    These simulate "Real World" complex usage and identify gaps.
-- ============================================================================
integrationTests :: TestTree
integrationTests = testGroup "Integration & Limitations"
  [ testGroup "Preliminary Successes"
    [ testCase "Polynomial Expansion and Collection: 4*(y + 1) - 6(y + 1) -> -2(1 + y)" $ do
        -- Input: 4(y+1) - 6(y+1)
        -- Expected: -2(1 + y)
        let y = mkSymbol "y"
            expr = (4 * (y + 1)) - (6 * (y + 1)) :: UnsimplifiedExpr
        automaticSimplify expr @?= Right (mkNumber (-2) * (1 + y))
    , testCase "Rational Arithmetic: 1/2 + 1/3 -> 5/6" $ do
        let expr = mkFraction 1 2 + mkFraction 1 3
        automaticSimplify expr @?= Right (mkFraction 5 6)
    ]

  , testGroup "Identified Limitations (Future Work)"
    [ testCase "Trigonometric Identity: sin^2(x) + cos^2(x) -> 1" $ do

        let x = mkSymbol "x"
            sinX = mkFunction "sin" (x :| [])
            cosX = mkFunction "cos" (x :| [])
            expr = (sinX ** 2) + (cosX ** 2) :: UnsimplifiedExpr

        case automaticSimplify expr of
             Right res -> res /= mkNumber 1 @?
              "System lacks Trig simplification"
             Left _    -> return ()
    ]
  ]
