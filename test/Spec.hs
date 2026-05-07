module Main (main) where 

import           Test.Tasty
import qualified SymHask.DifferentiaionSpec as Differentiation
import qualified SymHask.SimplificationSpec as Simplification

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "SymHask Tests"
  [
  Differentiation.tests,
  Simplification.tests
  ]