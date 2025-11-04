{-# LANGUAGE OverloadedStrings #-}

module Main
    ( main
    ) where

-- import           Control.Monad.IO.Class                (MonadIO (liftIO))
-- import qualified Data.HashSet                          as HS
-- import qualified Data.List.NonEmpty                    as NE
-- import           Data.Text                             (Text)
-- import qualified Data.Text                             as T
-- import           SymHask.Display.Haskell          (toHaskell)
-- import           SymHask.Symbolic.Analysis
-- import           SymHask.Symbolic.Differentiation
-- import           SymHask.Symbolic.Manipulation
-- import           SymHask.Symbolic.Simplification
-- import SymHask.Symbolic.Analysis

-- testMax :: [UnsimplifiedExpr] -> IO ()
-- testMax exprs = do
--   simplifiedExprs <- mapM (\e -> case simplify e of
--                               Left err -> error $ "Simplification error: " ++ show err
--                               Right simplified -> return simplified) exprs
--   putStrLn $ "Set of expressions: " ++ "(" ++ show (map toHaskell simplifiedExprs) ++ ")"
--   case maxExpr (HS.fromList simplifiedExprs) of
--     Left err -> error $ "Max expression error: " ++ show err
--     Right result -> putStrLn $ "Max expression: " ++ T.unpack (toHaskell result)


-- nestedMax :: EvalResult SimplifiedExpr
-- nestedMax = maxExpr (HS.fromList
--   [ mkNumber 1
--   , mkMax (HS.fromList [mkNumber 2, mkNumber 3])
--   , mkFunction "max" (NE.fromList [mkNumber 0, mkNumber 5])
--   ])

-- testMaxExponent :: UnsimplifiedExpr-> Text -> IO ()
-- testMaxExponent exprs var = do
--   case simplify exprs of
--     Left err -> error $ "Simplification error: " ++ show err
--     Right simplifiedExpr -> do
--       putStrLn $ "Expression: " ++ T.unpack (toHaskell simplifiedExpr)
--       case maxExponent simplifiedExpr var of
--         Left err -> error $ "Max expression error: " ++ show err
--         Right result -> putStrLn $ "Max expression: " ++ T.unpack (toHaskell result)
--   putStrLn ""


-- testAbs :: UnsimplifiedExpr -> IO ()
-- testAbs expr = do
--   case simplify expr of
--     Left err -> error $ "Simplification error: " ++ show err
--     Right simplifiedExpr -> do
--       putStrLn $ "Expression: " ++ T.unpack (toHaskell simplifiedExpr)
--       case absExpr simplifiedExpr of
--         Left err -> error $ "Abs expression error: " ++ show err
--         Right result -> putStrLn $ "Abs expression: " ++ T.unpack (toHaskell result)
--   putStrLn ""

-- testSeparateFactors :: UnsimplifiedExpr -> UnsimplifiedExpr -> IO ()
-- testSeparateFactors expr var = do
--   case (simplify expr, simplify var) of
--     (Right simplifiedExpr, Right simplifiedVar) -> do
--       putStrLn $ "Expression: " ++ T.unpack (toHaskell simplifiedExpr)
--       putStrLn $ "Variable: " ++ T.unpack (toHaskell simplifiedVar)
--       case separateFactors simplifiedExpr simplifiedVar of
--         Left err -> error $ "Separate factors error: " ++ show err
--         Right (freePart, depPart) -> do
--           putStrLn $ "Free part: " ++ T.unpack (toHaskell freePart)
--           putStrLn $ "Dependent part: " ++ T.unpack (toHaskell depPart)
--     (Left err, _) -> error $ "Simplification error (expr): " ++ show err
--     (_, Left err) -> error $ "Simplification error (var): " ++ show err
--   putStrLn ""

-- testLinearForm :: UnsimplifiedExpr -> Text -> IO ()
-- testLinearForm expr var = do
--   case simplify expr of
--     Left err -> error $ "Simplification error: " ++ show err
--     Right simplifiedExpr -> do
--       putStrLn $ "Expression: " ++ T.unpack (toHaskell simplifiedExpr)
--       case linearForm simplifiedExpr var of
--         Left err -> error $ "Linear form error: " ++ show err
--         Right isLinear -> case isLinear of
--           Just (LinearForm coefficient u) ->
--             putStrLn $ "The expression is linear in " ++ T.unpack var ++ " with coefficient: "
--             ++ T.unpack (toHaskell coefficient) ++ " and constant: " ++ T.unpack (toHaskell u)
--           Nothing -> putStrLn $ "The expression is not linear in " ++ T.unpack var
--   putStrLn ""

-- main :: IO ()
-- main = do
--   -- let exprSet1 = [ "a", 2, 3]
--   -- testMax exprSet1

--   -- let exprSet2 = [ "m", "m" + 1]
--   -- testMax exprSet2

--   -- let exprSet3 = [-5, "m", "m" + 1, 2, 3, sqrt 2]
--   -- testMax exprSet3

--   -- putStrLn "Testing nested max expression:"
--   -- case nestedMax of
--   --   Left err -> error $ "Nested max expression error: " ++ show err
--   --   Right result -> putStrLn $ "Nested max expression: " ++ T.unpack (toHaskell result)

--   -- testMaxExponent ("x" ** 2 + "x" ** 3) "x"
--   -- testMaxExponent ("x" + "x" ** (-1) + "x") "x"
--   -- testMaxExponent ("x"**2 + "x"**"m") "x"
--   -- testMaxExponent ("x"**("x"**2)*"x") "x"

--   -- testAbs $ "x" + 2 * I'
--   -- testAbs $ - (1 / 2)
--   -- testAbs $ (-2) * "x"
--   -- testAbs $ "x" + "y"

--   testAbs $ - (1 / 2)
--   testAbs $ (-2) * "x"
--   testAbs $ "x" + "y"
--   testAbs $ "x" + 2 * I'
--   testAbs (sqrt (1 - sqrt (2 - sqrt 5)) + I')
--   testLinearForm (sqrt (1 - sqrt (2 - sqrt 5)) + I') "i"

-- a :: UnsimplifiedExpr
-- a = (1 + (1 + (1 + (-1) * (2 + (-1) * 5 ** (1 / 2)) ** (1 / 2)) ** (1 / 2)) ** 2) ** (1 / 2)

main :: IO ()
main = putStrLn "Main module loaded."