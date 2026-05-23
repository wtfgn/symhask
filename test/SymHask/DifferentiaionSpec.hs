{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SymHask.DifferentiaionSpec
    ( tests
    ) where

import           Data.List.NonEmpty                        (NonEmpty ((:|)))
import qualified Data.List.NonEmpty                        as NE
import           SymHask.Symbolic                          (ExprError (..),
                                                            SimplifiedExpr,
                                                            Simplify (simplify),
                                                            UnsimplifiedExpr,
                                                            mkFraction,
                                                            mkFunction,
                                                            mkNumber, mkProduct,
                                                            mkSum, mkSymbol,
                                                            pattern (:**:),
                                                            pattern (:*:),
                                                            pattern (:+:),
                                                            pattern Acos',
                                                            pattern Acosh',
                                                            pattern Acot',
                                                            pattern Acoth',
                                                            pattern Acsc',
                                                            pattern Acsch',
                                                            pattern Asec',
                                                            pattern Asech',
                                                            pattern Asin',
                                                            pattern Asinh',
                                                            pattern Atan',
                                                            pattern Atanh',
                                                            pattern Cos',
                                                            pattern Cosh',
                                                            pattern Cot',
                                                            pattern Coth',
                                                            pattern Csc',
                                                            pattern Csch',
                                                            pattern Exp',
                                                            pattern Log',
                                                            pattern LogBase',
                                                            pattern Sec',
                                                            pattern Sech',
                                                            pattern Sin',
                                                            pattern Sinh',
                                                            pattern Sqrt',
                                                            pattern Tan',
                                                            pattern Tanh',
                                                            unsimplify)
import qualified SymHask.Symbolic.Calculus                 as Calc
import qualified SymHask.Symbolic.Calculus.Differentiation as Internal
import           Test.Tasty                                (TestTree, testGroup)
import           Test.Tasty.HUnit                          (Assertion,
                                                            assertFailure,
                                                            testCase, (@?=))
import           Test.Tasty.QuickCheck                     (Gen, choose,
                                                            elements, forAll,
                                                            frequency, oneof,
                                                            sized, testProperty,
                                                            vectorOf)
import           TestUtils                                 (arbitraryExpr)

tests :: TestTree
tests =
  testGroup
    "Differentiation"
    [ mkDiffVarTests
    , internalRuleTests
    , publicApiTests
    , propertyTests
    ]

-- ============================================================================
-- Helpers
-- ============================================================================

assertRight :: (Show e) => Either e a -> (a -> Assertion) -> Assertion
assertRight result check =
  case result of
    Right value -> check value
    Left err -> assertFailure ("Expected Right value, got Left: " <> show err)

mkX :: UnsimplifiedExpr
mkX = mkSymbol "x"

mkY :: UnsimplifiedExpr
mkY = mkSymbol "y"

mkZ :: UnsimplifiedExpr
mkZ = mkSymbol "z"

mkSX :: SimplifiedExpr
mkSX = mkSymbol "x"

mkSY :: SimplifiedExpr
mkSY = mkSymbol "y"

mkVarX :: Either ExprError Internal.DiffVar
mkVarX = Internal.mkDiffVar mkX

freeOfXExpr :: Int -> Gen UnsimplifiedExpr
freeOfXExpr 0 =
  oneof
    [ mkNumber <$> choose (-8, 8)
    , mkSymbol <$> elements ["y", "z", "a", "b"]
    ]
freeOfXExpr n =
  frequency
    [ (3, freeOfXExpr 0)
    , (1, mkSum . NE.fromList <$> vectorOf 2 subExpr)
    , (1, mkProduct . NE.fromList <$> vectorOf 2 subExpr)
    , (1, mkPowerExpr)
    ]
 where
  subExpr = freeOfXExpr (n `div` 2)
  mkPowerExpr = do
    b <- subExpr
    e <- oneof [mkNumber <$> choose (0, 4), subExpr]
    pure $ b ** e

expectDiff :: UnsimplifiedExpr -> Internal.DiffVar -> Either ExprError UnsimplifiedExpr
expectDiff expr xVar = Internal.diff expr xVar >>= fmap unsimplify . simplify

-- ============================================================================
-- 1. mkDiffVar
-- ============================================================================

mkDiffVarTests :: TestTree
mkDiffVarTests =
  testGroup
    "mkDiffVar"
    [ testCase "Symbol becomes DiffSymbol" $
        fmap show (Internal.mkDiffVar mkX)
          @?= Right "DiffSymbol \"x\""
    , testCase "Function with symbol arguments becomes DiffFunction" $ do
        let expr = mkFunction "f" (mkX :| [mkY])
        fmap show (Internal.mkDiffVar expr)
          @?= Right "DiffFunction \"f\" (\"x\" :| [\"y\"])"
    , testCase "Numbers are rejected" $
        Internal.mkDiffVar (mkNumber 3)
          @?= Left (UnsupportedOperation "Cannot create DiffVar from this expression type")
    , testCase "Sums are rejected" $
        Internal.mkDiffVar (mkSum (mkX :| [mkY]))
          @?= Left (UnsupportedOperation "Cannot create DiffVar from this expression type")
    , testCase "Products are rejected" $
        Internal.mkDiffVar (mkProduct (mkX :| [mkY]))
          @?= Left (UnsupportedOperation "Cannot create DiffVar from this expression type")
    ]

-- ============================================================================
-- 2. Internal differentiation rules
-- ============================================================================

internalRuleTests :: TestTree
internalRuleTests =
  testGroup
    "Internal Rules"
    [ identityAndZeroTests
    , algebraicRuleTests
    , functionRuleTests
    ]

identityAndZeroTests :: TestTree
identityAndZeroTests =
  testGroup
    "Identity and Zero"
    [ testCase "d/dx x = 1" $
        assertRight mkVarX $
          \xVar -> expectDiff mkX xVar @?= Right (mkNumber 1)
    , testCase "Constants differentiate to 0" $
        assertRight mkVarX $
          \xVar -> expectDiff (mkNumber 7) xVar @?= Right (mkNumber 0)
    , testCase "Different symbols are free of x and differentiate to 0" $
        assertRight mkVarX $
          \xVar -> expectDiff mkY xVar @?= Right (mkNumber 0)
    ]

algebraicRuleTests :: TestTree
algebraicRuleTests =
  testGroup
    "Algebraic Rules"
    [ testCase "Sum rule on three terms" $
        assertRight mkVarX $ \xVar ->
          expectDiff (mkSum (mkX :| [mkY, mkZ])) xVar
            @?= Right (mkNumber 1)
    , testCase "Product rule on two terms" $
        assertRight mkVarX $ \xVar ->
          expectDiff (mkX * mkY) xVar
            @?= Right mkY
    , testCase "Power rule with constant exponent" $
        assertRight mkVarX $ \xVar ->
          expectDiff (mkX ** mkNumber 2) xVar
            @?= Right (mkNumber 2 * mkX)
    , testCase "Power rule with variable exponent" $
        assertRight mkVarX $ \xVar ->
          expectDiff (mkX ** mkX) xVar
            @?= Right (mkX ** mkX + log mkX * mkX ** mkX)
    ]

functionRuleTests :: TestTree
functionRuleTests =
  testGroup
    "Function Rules"
    [ elementaryFunctionTests
    , trigonometricFunctionTests
    , inverseTrigonometricFunctionTests
    , hyperbolicFunctionTests
    , inverseHyperbolicFunctionTests
    , unknownFunctionTests
    ]

elementaryFunctionTests :: TestTree
elementaryFunctionTests =
  testGroup
    "Elementary"
    [ testCase "sqrt rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Sqrt' mkX) xVar @?= Right (mkFraction 1 2 * (mkX ** mkFraction (-1) 2))
    , testCase "exp rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Exp' mkX) xVar @?= Right (Exp' mkX)
    , testCase "log rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Log' mkX) xVar @?= Right (mkX ** mkNumber (-1))
    , testCase "logBase rule, derivative with respect to the value" $ do
        let expr = LogBase' mkX mkY
        assertRight mkVarX $ \xVar ->
          expectDiff expr xVar
            @?= Right (mkProduct (NE.fromList [mkNumber (-1), log mkX ** mkNumber (-2), log mkY, mkX ** mkNumber (-1)]))
    , testCase "logBase rule, derivative with respect to the base" $ do
        let expr = LogBase' mkX mkY
        assertRight (Internal.mkDiffVar mkY) $ \yVar ->
          expectDiff expr yVar
            @?= Right (log mkX ** mkNumber (-1) * mkY ** mkNumber (-1))
    ]

trigonometricFunctionTests :: TestTree
trigonometricFunctionTests =
  testGroup
    "Trigonometric"
    [ testCase "sin rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Sin' mkX) xVar @?= Right (Cos' mkX)
    , testCase "cos rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Cos' mkX) xVar @?= Right (mkNumber (-1) * Sin' mkX)
    , testCase "tan rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Tan' mkX) xVar @?= Right (Cos' mkX ** mkNumber (-2))
    , testCase "cot rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Cot' mkX) xVar @?= Right (mkNumber (-1) * Sin' mkX ** mkNumber (-2))
    , testCase "sec rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Sec' mkX) xVar @?= Right (Cos' mkX ** mkNumber (-2) * Sin' mkX)
    , testCase "csc rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Csc' mkX) xVar @?= Right (mkProduct (NE.fromList [mkNumber (-1), Cos' mkX, Sin' mkX ** mkNumber (-2)]))
    ]

inverseTrigonometricFunctionTests :: TestTree
inverseTrigonometricFunctionTests =
  testGroup
    "Inverse Trigonometric"
    [ testCase "asin rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Asin' mkX) xVar @?= Right ((mkNumber 1 + mkNumber (-1) * mkX ** mkNumber 2) ** mkFraction (-1) 2)
    , testCase "acos rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Acos' mkX) xVar @?= Right (mkProduct (NE.fromList [mkNumber (-1), (mkNumber 1 + mkNumber (-1) * mkX ** mkNumber 2) ** mkFraction (-1) 2]))
    , testCase "atan rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Atan' mkX) xVar @?= Right ((mkNumber 1 + mkX ** mkNumber 2) ** mkNumber (-1))
    , testCase "acot rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Acot' mkX) xVar @?= Right (mkNumber (-1) * (mkNumber 1 + mkX ** mkNumber 2) ** mkNumber (-1))
    , testCase "asec rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Asec' mkX) xVar @?= Right (abs mkX ** mkNumber (-1) * (mkNumber (-1) + mkX ** mkNumber 2) ** mkFraction (-1) 2)
    , testCase "acsc rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Acsc' mkX) xVar @?= Right (mkProduct (NE.fromList [mkNumber (-1), abs mkX ** mkNumber (-1), (mkNumber (-1) + mkX ** mkNumber 2) ** mkFraction (-1) 2]))
    ]

hyperbolicFunctionTests :: TestTree
hyperbolicFunctionTests =
  testGroup
    "Hyperbolic"
    [ testCase "sinh rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Sinh' mkX) xVar @?= Right (Cosh' mkX)
    , testCase "cosh rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Cosh' mkX) xVar @?= Right (Sinh' mkX)
    , testCase "tanh rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Tanh' mkX) xVar @?= Right (Cosh' mkX ** mkNumber (-2))
    , testCase "coth rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Coth' mkX) xVar @?= Right (mkNumber (-1) * (sinh mkX ** mkNumber (-2)))
    , testCase "sech rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Sech' mkX) xVar @?= Right (mkProduct (NE.fromList [mkNumber (-1), Cosh' mkX ** mkNumber (-2), Sinh' mkX]))
    , testCase "csch rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Csch' mkX) xVar @?= Right (mkProduct (NE.fromList [mkNumber (-1), Cosh' mkX, Sinh' mkX ** mkNumber (-2)]))
    ]

inverseHyperbolicFunctionTests :: TestTree
inverseHyperbolicFunctionTests =
  testGroup
    "Inverse Hyperbolic"
    [ testCase "asinh rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Asinh' mkX) xVar @?= Right ((mkNumber 1 + mkX ** mkNumber 2) ** mkFraction (-1) 2)
    , testCase "acosh rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Acosh' mkX) xVar @?= Right ((mkNumber (-1) + mkX ** mkNumber 2) ** mkFraction (-1) 2)
    , testCase "atanh rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Atanh' mkX) xVar @?= Right ((mkNumber 1 + mkNumber (-1) * mkX ** mkNumber 2) ** mkNumber (-1))
    , testCase "acoth rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Acoth' mkX) xVar @?= Right ((mkNumber 1 + mkNumber (-1) * mkX ** mkNumber 2) ** mkNumber (-1))
    , testCase "asech rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Asech' mkX) xVar @?= Right (mkProduct (NE.fromList [mkNumber (-1), mkX ** mkNumber (-1), (mkNumber 1 + mkNumber (-1) * mkX ** mkNumber 2) ** mkFraction (-1) 2]))
    , testCase "acsch rule" $
        assertRight mkVarX $ \xVar ->
          expectDiff (Acsch' mkX) xVar @?= Right (mkProduct (NE.fromList [mkNumber (-1), abs mkX ** mkNumber (-1), (mkNumber 1 + mkX ** mkNumber 2) ** mkFraction (-1) 2]))
    ]

unknownFunctionTests :: TestTree
unknownFunctionTests =
  testGroup
    "Unknown Functions"
    [ testCase "generalized chain rule introduces a symbolic derivative placeholder" $ do
        assertRight mkVarX $ \xVar -> do
          let expr = mkFunction "f" (mkX :| [mkY])
          expectDiff expr xVar @?= Right (mkFunction "diff" (expr :| [mkX]))
    , testCase "unknown function with an unrelated variable falls back to 0" $ do
        assertRight mkVarX $ \xVar ->
          expectDiff (mkFunction "f" (mkY :| [mkZ])) xVar @?= Right (mkNumber 0)
    ]

-- ============================================================================
-- 3. Public API checks
-- ============================================================================

publicApiTests :: TestTree
publicApiTests =
  testGroup
    "Public API"
    [ testCase "diff simplifies a sum" $ do
        let Right xVar = Calc.mkDiffVar mkSX
        Calc.diff xVar (mkSX :+: mkSY) @?= Right (mkNumber 1)
    , testCase "diff simplifies a product" $ do
        let Right xVar = Calc.mkDiffVar mkSX
        Calc.diff xVar (mkSX :*: mkSY) @?= Right mkSY
    , testCase "diff of sin is cos" $ do
        let Right xVar = Calc.mkDiffVar mkSX
        Calc.diff xVar (Sin' mkSX) @?= Right (Cos' mkSX)
    , testCase "diff of exp is exp" $ do
        let Right xVar = Calc.mkDiffVar mkSX
        Calc.diff xVar (Exp' mkSX) @?= Right (Exp' mkSX)
    , testCase "multiDiff applies repeated differentiation" $ do
        let Right xVar = Calc.mkDiffVar mkSX
        let Right yVar = Calc.mkDiffVar mkSY
        Calc.multiDiff [xVar, yVar] mkSX @?= Right (mkNumber 0)
    ]

-- ============================================================================
-- 4. Property tests
-- ============================================================================

propertyTests :: TestTree
propertyTests =
  testGroup
    "Properties"
    [ testProperty "free-of-x expressions differentiate to zero" $
        forAll (sized freeOfXExpr) $ \expr ->
          case mkVarX of
            Right xVar -> expectDiff expr xVar == Right (mkNumber 0)
            Left _     -> False
    , testProperty "sum rule is linear" $
        forAll (sized arbitraryExpr) $ \a ->
          forAll (sized arbitraryExpr) $ \b ->
            case mkVarX of
              Right xVar ->
                let lhs = Internal.diff (a + b) xVar
                    rhs = case (Internal.diff a xVar, Internal.diff b xVar) of
                      (Right da, Right db) -> Right (da + db)
                      (Left err, _)        -> Left err
                      (_, Left err)        -> Left err
                 in lhs == rhs
              Left _ -> False
              -- testProperty "product rule matches the expected two-factor expansion" $
              --   forAll (sized arbitraryExpr) $ \a ->
              --     forAll (sized arbitraryExpr) $ \b ->
              --       case mkVarX of
              --         Right xVar ->
              --           let lhs = expectDiff (a * b) xVar
              --               rhs = case (Internal.diff a xVar, Internal.diff b xVar) of
              --                 (Right da, Right db) -> unsimplify <$> simplify (da * b + a * db)
              --                 (Left err, _) -> Left err
              --                 (_, Left err) -> Left err
              --            in lhs == rhs
              --         Left _ -> False
    ]
