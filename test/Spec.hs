module Main (main) where

import qualified SymHask.DifferentiaionSpec as Differentiation
import qualified SymHask.IntegrationSpec as Integration
import qualified SymHask.PolynomialSpec as Polynomial
import qualified SymHask.SimplificationSpec as Simplification
import qualified SymHask.TranscendentalSpec as Transcendental
import Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "SymHask Tests"
    [ Differentiation.tests,
      Simplification.tests,
      Integration.tests,
      Polynomial.tests,
      Transcendental.tests
    ]