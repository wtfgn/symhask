-- | This serve as an example of how to use the library,
-- and also provides a simple interactive shell for testing out expressions.
--
-- Most of the code here is just parsing and user interaction, the core logic is in SymHask.
--
-- The full capabilities of the library are not exposed in this shell,
-- but it should be enough to demonstrate its use.
module Main
    ( main
    ) where

import           Control.Applicative          (many, optional, (<|>))
import           Control.Monad                (unless)
import           Data.Char                    (isAlphaNum, isDigit)
import qualified Data.List.NonEmpty           as NE
import qualified Data.Map.Strict              as M
import           Data.Maybe                   (fromMaybe)
import           Data.Text                    (Text)
import qualified Data.Text                    as T
import qualified Data.Text.IO                 as TIO
import           System.Exit                  (exitSuccess)
import           System.IO                    (hFlush, isEOF, stdout)
import           Text.ParserCombinators.ReadP (ReadP, chainl1, eof, look, munch,
                                               munch1, pfail, readP_to_S,
                                               satisfy, sepBy1, skipSpaces,
                                               string)

import           SymHask

-- main = pure ()

type Env = M.Map Text UnsimplifiedExpr

data OutputMode
  = Bare
  | HaskellMode
  | LatexMode

main :: IO ()
main = do
        TIO.putStrLn "SymHask interactive shell"
        TIO.putStrLn "Type :help for commands, :quit to exit."
        repl M.empty

repl :: Env -> IO ()
repl env = do
        TIO.putStr "symhask> "
        hFlush stdout
        done <- isEOF
        if done
            then pure ()
            else do
                line <- TIO.getLine
                (nextEnv, shouldExit) <- handleLine env line
                unless shouldExit $ repl nextEnv

handleLine :: Env -> Text -> IO (Env, Bool)
handleLine env rawLine =
        case T.strip rawLine of
            "" -> pure (env, False)
            line
                | T.isPrefixOf ":" line -> handleCommand env (T.words line)
                | Just (name, exprText) <- parseBindingLine line -> bindName env name exprText
                | otherwise -> runExpression env Bare line

handleCommand :: Env -> [Text] -> IO (Env, Bool)
handleCommand env = \case
        ":quit" : _ -> pure (env, True)
        ":q" : _ -> pure (env, True)
        ":exit" : _ -> pure (env, True)
        ":help" : _ -> printHelp >> pure (env, False)
        ":env" : _ -> printEnv env >> pure (env, False)
        ":latex" : rest -> runExpression env LatexMode (T.unwords rest)
        ":haskell" : rest -> runExpression env HaskellMode (T.unwords rest)
        ":simplify" : rest -> runExpression env Bare (T.unwords rest)
        ":diff" : var : rest -> runDiff env var (T.unwords rest)
        ":let" : rest ->
                case parseBindingLine (T.unwords rest) of
                    Just (name, exprText) -> bindName env name exprText
                    Nothing -> reportParseError env "Expected :let name = expression"
        _ -> TIO.putStrLn "Unknown command. Type :help for usage." >> pure (env, False)

bindName :: Env -> Text -> Text -> IO (Env, Bool)
bindName env name exprText =
        case parseExpr env exprText of
            Left err -> reportParseError env err
            Right expr -> do
                let nextEnv = M.insert name expr env
                TIO.putStrLn $ name <> " = " <> toHaskell expr
                pure (nextEnv, False)

runExpression :: Env -> OutputMode -> Text -> IO (Env, Bool)
runExpression env mode exprText =
        case parseExpr env exprText of
            Left err -> reportParseError env err
            Right expr ->
                case simplify expr of
                    Left err -> TIO.putStrLn (formatError err) >> pure (env, False)
                    Right value -> do
                        case mode of
                            Bare        -> TIO.putStrLn (toHaskell value)
                            HaskellMode -> TIO.putStrLn (toHaskell value)
                            LatexMode   -> TIO.putStrLn (toLaTeX value)
                        pure (env, False)

runDiff :: Env -> Text -> Text -> IO (Env, Bool)
runDiff env var exprText =
        case parseExpr env exprText of
            Left err -> reportParseError env err
            Right expr ->
                case mkDiffVar (mkSymbol var) of
                    Left err -> TIO.putStrLn (formatError err) >> pure (env, False)
                    Right diffVar ->
                        case diff diffVar expr of
                            Left err -> TIO.putStrLn (formatError err) >> pure (env, False)
                            Right value -> TIO.putStrLn (toHaskell value) >> pure (env, False)

reportParseError :: Env -> Text -> IO (Env, Bool)
reportParseError env err = TIO.putStrLn err >> pure (env, False)

parseExpr :: Env -> Text -> Either Text UnsimplifiedExpr
parseExpr env input =
        case [expr | (expr, rest) <- readP_to_S (skipSpaces *> exprP env <* skipSpaces <* eof) (T.unpack input), null rest] of
            expr : _ -> Right expr
            []       -> Left "Could not parse expression."

exprP :: Env -> ReadP UnsimplifiedExpr
exprP env = sumP env

sumP :: Env -> ReadP UnsimplifiedExpr
sumP env = chainl1 (productP env) sumOp
 where
    sumOp =
                (skipSpaces *> string "+" *> skipSpaces *> pure (+))
        <|> (skipSpaces *> string "-" *> skipSpaces *> pure (-))

productP :: Env -> ReadP UnsimplifiedExpr
productP env = chainl1 (powerP env) productOp
 where
    productOp =
                (skipSpaces *> string "*" *> skipSpaces *> pure (*))
        <|> (skipSpaces *> string "/" *> skipSpaces *> pure (/))

powerP :: Env -> ReadP UnsimplifiedExpr
powerP env = do
        base <- postfixP env
        rest <- optional (skipSpaces *> string "^" *> skipSpaces *> powerP env)
        pure $ maybe base (base **) rest

postfixP :: Env -> ReadP UnsimplifiedExpr
postfixP env = do
        core <- unaryP env
        suffixes <- many (skipSpaces *> string "!")
        pure $ foldl (\acc _ -> (!) acc) core suffixes

unaryP :: Env -> ReadP UnsimplifiedExpr
unaryP env =
                (skipSpaces *> string "-" *> skipSpaces *> (negate <$> unaryP env))
        <|> primaryP env

primaryP :: Env -> ReadP UnsimplifiedExpr
primaryP env =
                numberP
        <|> constantP
        <|> parens (exprP env)
        <|> functionOrSymbolP env

numberP :: ReadP UnsimplifiedExpr
numberP = mkNumber . read <$> munch1 isDigit

constantP :: ReadP UnsimplifiedExpr
constantP =
                keyword "pi" Pi'
        <|> keyword "e" E'
        <|> keyword "i" I'

keyword :: String -> UnsimplifiedExpr -> ReadP UnsimplifiedExpr
keyword name value = do
        _ <- string name
        notFollowedByIdentChar
        pure value

functionOrSymbolP :: Env -> ReadP UnsimplifiedExpr
functionOrSymbolP env = do
        name <- identifierP
        rest <- look
        case rest of
            '(' : _ -> functionCallParens env name
            _ | name `elem` unaryFunctionNames -> do
                        arg <- skipSpaces *> powerP env
                        pure $ mkFunction name (arg NE.:| [])
                | name == "logBase" -> do
                        base <- skipSpaces *> powerP env
                        arg <- skipSpaces *> powerP env
                        pure $ mkFunction name (base NE.:| [arg])
                | otherwise -> pure $ resolveSymbol env name

functionCallParens :: Env -> Text -> ReadP UnsimplifiedExpr
functionCallParens env name = do
        args <- parens (exprP env `sepBy1` commaP)
        pure $ mkFunction name (NE.fromList args)

identifierP :: ReadP Text
identifierP = do
        first <- firstChar
        rest <- munch restChar
        let ident = first : rest
        notFollowedByIdentChar
        pure (T.pack ident)
 where
    firstChar = satisfyIdentStart
    restChar c = isAlphaNum c || c == '_' || c == '\''

satisfyIdentStart :: ReadP Char
satisfyIdentStart = do
        c <- satisfy isIdentStart
        pure c
 where
    isIdentStart ch = isAlphaNum ch || ch == '_'

commaP :: ReadP Char
commaP = skipSpaces *> string "," *> skipSpaces *> pure ','

parens :: ReadP a -> ReadP a
parens p = skipSpaces *> string "(" *> skipSpaces *> p <* skipSpaces <* string ")"

notFollowedByIdentChar :: ReadP ()
notFollowedByIdentChar = do
        next <- look
        case next of
            c : _ | isAlphaNum c || c == '_' || c == '\'' -> pfail
            _                                             -> pure ()

resolveSymbol :: Env -> Text -> UnsimplifiedExpr
resolveSymbol env name = fromMaybe (mkSymbol name) (M.lookup name env)

parseBindingLine :: Text -> Maybe (Text, Text)
parseBindingLine line =
        case T.stripPrefix "let " line of
            Just rest -> splitBinding rest
            Nothing   -> splitBinding line
 where
    splitBinding txt =
        let (lhs, rhs) = T.breakOn "=" txt
        in case T.stripPrefix "=" rhs of
                 Just exprText
                     | not (T.null (T.strip lhs))
                     , validBindingName (T.strip lhs) -> Just (T.strip lhs, T.strip exprText)
                 _ -> Nothing

    validBindingName name = not (T.null name) && T.all isBindingChar name
    isBindingChar c = isAlphaNum c || c == '_' || c == '\''

printHelp :: IO ()
printHelp = do
        TIO.putStrLn "Commands:"
        TIO.putStrLn "  :help                Show this help"
        TIO.putStrLn "  :quit | :q | :exit   Leave the shell"
        TIO.putStrLn "  :env                 Show current bindings"
        TIO.putStrLn "  :latex EXPR          Print LaTeX output"
        TIO.putStrLn "  :haskell EXPR        Print Haskell-style output"
        TIO.putStrLn "  :simplify EXPR       Simplify and print the result"
        TIO.putStrLn "  :diff x EXPR         Differentiate EXPR with respect to x"
        TIO.putStrLn "  let x = EXPR         Bind a name for later use"
        TIO.putStrLn ""
        TIO.putStrLn "Syntax: +, -, *, /, ^, !, parentheses, and calls like sin x or logBase 2 x"

printEnv :: Env -> IO ()
printEnv env
        | M.null env = TIO.putStrLn "(no bindings)"
        | otherwise = mapM_ printBinding (M.toList env)
 where
    printBinding (name, expr) = TIO.putStrLn $ name <> " = " <> toHaskell expr

formatError :: ExprError -> Text
formatError = \case
        DivisionByZero -> "Division by zero"
        InvalidDomain msg -> "Invalid domain: " <> msg
        UnsupportedOperation msg -> "Unsupported operation: " <> msg
        EvaluationFailure msg -> "Evaluation failure: " <> msg

unaryFunctionNames :: [Text]
unaryFunctionNames =
        [ "abs", "acosh", "acot", "acoth", "acsc", "acsch", "asec", "asech"
        , "asin", "asinh", "atan", "atanh", "cos", "cosh", "cot", "coth"
        , "csc", "csch", "exp", "log", "negate", "sec", "sech", "signum"
        , "sin", "sinh", "sqrt", "tan", "tanh"
        ]
