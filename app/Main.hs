{-# LANGUAGE OverloadedStrings #-}

module Main
    ( main
    ) where

import           Control.Monad.IO.Class                    ()
import qualified Data.HashSet                              as HS
import qualified Data.List.NonEmpty                        as NE
import           Data.Text                                 (Text)
import qualified Data.Text                                 as T
import           SymHask.Printer.Haskell                   (toHaskell)
import           SymHask.Symbolic
import           SymHask.Symbolic.Basic
import           SymHask.Symbolic.Calculus
import           SymHask.Symbolic.Simplification ()

testDiff :: UnsimplifiedExpr -> Text -> IO ()
testDiff expr varName = do
  case simplify expr of
    Left err -> error $ "Simplification error: " ++ show err
    Right simplifiedExpr -> do
      putStrLn $ "Expression: " ++ T.unpack (toHaskell simplifiedExpr)
      dVar <- case mkDiffVar (mkSymbol varName) of
                Left err -> error $ "mkDiffVar error: " ++ show err
                Right dv -> return dv
      case diff simplifiedExpr dVar of
        Left err -> error $ "Differentiation error: " ++ show err
        Right result -> putStrLn $ "Derivative w.r.t. " ++ T.unpack varName ++ ": "
                          ++ T.unpack (toHaskell result)
                          ++ "\n"
                          --  print the raw result for debugging
                          ++ "Raw derivative: " ++ show result
  putStrLn ""

testMax :: [UnsimplifiedExpr] -> IO ()
testMax exprs = do
  simplifiedExprs <- mapM (\e -> case simplify e of
                              Left err -> error $ "Simplification error: " ++ show err
                              Right simplified -> return simplified) exprs
  putStrLn $ "Set of expressions: " ++ "(" ++ show (map toHaskell simplifiedExprs) ++ ")"
  case evalMax (HS.fromList simplifiedExprs) of
    Left err     -> error $ "Max expression error: " ++ show err
    Right result -> putStrLn $ "Max expression: " ++ T.unpack (toHaskell result)


nestedMax :: EvalResult SimplifiedExpr
nestedMax = evalMax (HS.fromList
  [ mkNumber 1
  , mkMax (HS.fromList [mkNumber 2, mkNumber 3])
  , mkFunction "max" (NE.fromList [mkNumber 0, mkNumber 5])
  ])


testAbs :: UnsimplifiedExpr -> IO ()
testAbs expr = do
  case simplify expr of
    Left err -> error $ "Simplification error: " ++ show err
    Right simplifiedExpr -> do
      putStrLn $ "Expression: " ++ T.unpack (toHaskell simplifiedExpr)
      case evalAbs simplifiedExpr of
        Left err -> error $ "Abs expression error: " ++ show err
        Right result -> putStrLn $ "Abs expression: " ++ T.unpack (toHaskell result)
  putStrLn ""

testSeparateFactors :: UnsimplifiedExpr -> UnsimplifiedExpr -> IO ()
testSeparateFactors expr var = do
  case (simplify expr, simplify var) of
    (Right simplifiedExpr, Right simplifiedVar) -> do
      putStrLn $ "Expression: " ++ T.unpack (toHaskell simplifiedExpr)
      putStrLn $ "Variable: " ++ T.unpack (toHaskell simplifiedVar)
      case separateFactors simplifiedExpr simplifiedVar of
        Left err -> error $ "Separate factors error: " ++ show err
        Right (freePart, depPart) -> do
          putStrLn $ "Free part: " ++ T.unpack (toHaskell freePart)
          putStrLn $ "Dependent part: " ++ T.unpack (toHaskell depPart)
    (Left err, _) -> error $ "Simplification error (expr): " ++ show err
    (_, Left err) -> error $ "Simplification error (var): " ++ show err
  putStrLn ""

testLinearForm :: UnsimplifiedExpr -> Text -> IO ()
testLinearForm expr var = do
  case simplify expr of
    Left err -> error $ "Simplification error: " ++ show err
    Right simplifiedExpr -> do
      putStrLn $ "Expression: " ++ T.unpack (toHaskell simplifiedExpr)
      case linearForm simplifiedExpr var of
        Left err -> error $ "Linear form error: " ++ show err
        Right isLinear -> case isLinear of
          Just (LinearForm coefficient u) ->
            putStrLn $ "The expression is linear in " ++ T.unpack var ++ " with coefficient: "
            ++ T.unpack (toHaskell coefficient) ++ " and constant: " ++ T.unpack (toHaskell u)
          Nothing -> putStrLn $ "The expression is not linear in " ++ T.unpack var
  putStrLn ""

main :: IO ()
main = do
  -- let exprSet1 = [ "a", 2, 3]
  -- testMax exprSet1

  -- let exprSet2 = [ "m", "m" + 1]
  -- testMax exprSet2

  -- let exprSet3 = [-5, "m", "m" + 1, 2, 3, sqrt 2]
  -- testMax exprSet3

  -- putStrLn "Testing nested max expression:"
  -- case nestedMax of
  --   Left err -> error $ "Nested max expression error: " ++ show err
  --   Right result -> putStrLn $ "Nested max expression: " ++ T.unpack (toHaskell result)

  -- testMaxExponent ("x" ** 2 + "x" ** 3) "x"
  -- testMaxExponent ("x" + "x" ** (-1) + "x") "x"
  -- testMaxExponent ("x"**2 + "x"**"m") "x"
  -- testMaxExponent ("x"**("x"**2)*"x") "x"

  -- testAbs $ "x" + 2 * I'
  -- testAbs $ - (1 / 2)
  -- testAbs $ (-2) * "x"
  -- testAbs $ "x" + "y"

  -- testAbs $ - (1 / 2)
  -- testAbs $ (-2) * "x"
  -- testAbs $ "x" + "y"
  -- testAbs $ "x" + 2 * I'
  -- testAbs (sqrt (1 - sqrt (2 - sqrt 5)) + I')
  -- testLinearForm (sqrt (1 - sqrt (2 - sqrt 5)) + I') "i"

  -- testDiff ("x" ** 3 + 2 * "x" ** 2 + "x" + 5) "x"
  -- testDiff (sin ("x" ** 2) + exp "x" + log "x") "x"
  -- testDiff (("x" ** "x") + logBase 2 "x") "x"
  -- testDiff (("x" ** 2 + "x" + 1) * ("x" + 3)) "x"
  -- testDiff (sqrt ("x" ** 2 + 1)) "x"
  -- testDiff ("x" ** 3 + 2 * "x" ** 2 + "x" + 5) "x"
  testDiff ("x" * "y") "x"
  testDiff ("x" ** "x") "x"
  testDiff (logBase "x" "y") "x"
  testDiff (Asin' "x") "x"
  testDiff ("b" ** (0 ** (mkNumber (-1)) + "a")) "x"

  -- runDiff example
  case runDiff of
    Left err -> error $ "runDiff error: " ++ show err
    Right result -> putStrLn $ "Result of runDiff: " ++ T.unpack (toHaskell result)

runDiff :: EvalResult SimplifiedExpr
runDiff = do
  expr' <- simplify expr
  d1 <- diff expr' =<< mkDiffVar x
  d2 <- diff d1 =<< mkDiffVar x
  simplify d2
  where
    x = mkSymbol "x"
    expr :: UnsimplifiedExpr
    expr = x ** 3 + 2 * x ** 2 + x + 5 


-- Test commit