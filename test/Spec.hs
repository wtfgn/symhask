module Main (main) where 

import           Test.Tasty
import qualified SymHask.SimplificationSpec as Simplification

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "SymHask Tests"
  [
  Simplification.tests
  ]