{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}

module SymHask.Symbolic.Basic
  ( FunctionParity (..),
    LinearForm (..),
    Substitution.Pattern (..),
    Substitution.Replacement (..),
    completeSubExprs,
    trialSubstitutions,
    concurSubs,
    evalAbs,
    evalMax,
    evenOdd,
    exponents,
    freeOf,
    linearForm,
    operands,
    separateFactors,
    seqSubs,
    subs,
    symbols,
    treeSize,
  )
where

import Control.Monad
import Control.Monad.Error.Class (throwError)
import qualified Data.HashSet as HS
import qualified Data.List.NonEmpty as NE
import Data.Text (Text)
import SymHask.Symbolic
import qualified SymHask.Symbolic.Basic.Substitution as Substitution
import SymHask.Symbolic.Basic.Utils
import SymHask.Symbolic.Simplification

data FunctionParity
  = EvenFunc
  | OddFunc
  | NeitherFunc
  deriving (Eq, Show)

-- | A linear form represented as a*x + b
data LinearForm
  = LinearForm
  { coeffTerm :: SimplifiedExpr,
    -- Coefficient of x
    constTerm :: SimplifiedExpr
    -- Constant term
  }
  deriving (Eq, Show)

treeSize :: SimplifiedExpr -> Int
treeSize = \case
  Number' _ -> 1
  Fraction' _ _ -> 3
  Symbol' _ -> 1
  Quotient' n d -> 1 + treeSize n + treeSize d
  UnaryDiff' x -> 1 + treeSize x
  BinaryDiff' x y -> 1 + treeSize x + treeSize y
  Product' factors -> 1 + sum (NE.map treeSize factors)
  Sum' terms -> 1 + sum (NE.map treeSize terms)
  Power' b e -> 1 + treeSize b + treeSize e
  Factorial' expr -> 1 + treeSize expr
  Function' _ args -> 1 + sum (NE.map treeSize args)

completeSubExprs :: SimplifiedExpr -> HS.HashSet SimplifiedExpr
completeSubExprs expr
  | null (operands expr) = HS.singleton expr
  | otherwise = HS.insert expr (HS.unions subSets)
  where
    subSets = map completeSubExprs $ operands expr

-- | Trial substitutions: collect candidate subexpressions suitable for
-- substitution. This returns a set containing:
--  * function applications (Function' name args)
--  * arguments of function applications
--  * bases and exponents of power expressions
-- The result is a HashSet of `SimplifiedExpr`.
trialSubstitutions :: SimplifiedExpr -> HS.HashSet SimplifiedExpr
trialSubstitutions expr = HS.foldl' collect HS.empty (completeSubExprs expr)
  where
    collect acc e@(Function' _ args) =
      let acc' = HS.insert e acc
          argSet = HS.fromList (NE.toList args)
       in HS.union acc' argSet
    collect acc (Power' b ex) = HS.insert b $ HS.insert ex acc
    collect acc _ = acc

-- | Separate factors into parts free of variable x and parts dependent on x
-- For expression u*v*w..., separates into (free_part, dependent_part) where:
-- - free_part contains factors that don't depend on x
-- - dependent_part contains factors that do depend on x
separateFactors :: SimplifiedExpr -> SimplifiedExpr -> EvalResult (SimplifiedExpr, SimplifiedExpr)
separateFactors (Product' factors) var =
  foldM processFactor (mkNumber 1, mkNumber 1) (NE.toList factors)
  where
    -- Process a single factor
    processFactor ::
      (SimplifiedExpr, SimplifiedExpr) ->
      SimplifiedExpr ->
      EvalResult (SimplifiedExpr, SimplifiedExpr)
    processFactor (currFree, currDep) factor = do
      -- if freeOf(f, x) then
      if freeOf factor var
        then do
          -- free_of_part := f * free_of_part
          newFree <- factor .*. currFree
          return (newFree, currDep)
        else do
          -- dependent_part := f * dependent_part
          newDependent <- factor .*. currDep
          return (currFree, newDependent)

-- Handle non-product expressions
separateFactors expr var = do
  -- if freeOf(u, x) then (u, 1)
  if freeOf expr var
    then return (expr, mkNumber 1)
    -- else (1, u)
    else return (mkNumber 1, expr)

evenOdd :: SimplifiedExpr -> Text -> EvalResult FunctionParity
evenOdd expr x = do
  negX <- simplify (negate (mkSymbol x) :: UnsimplifiedExpr)
  substituted <-
    subs
      (Substitution.Pattern (mkSymbol x), Substitution.Replacement negX)
      expr
  if
    | expr .-. substituted == pure (mkNumber 0) -> return EvenFunc
    | expr .+. substituted == pure (mkNumber 0) -> return OddFunc
    | otherwise -> return NeitherFunc

evalAbs :: SimplifiedExpr -> EvalResult SimplifiedExpr
evalAbs (Number' n) = pure $ mkNumber (abs n)
evalAbs (Fraction' n d) = simplify $ mkFraction (abs n) (abs d)
evalAbs (Product' factors) = mapM evalAbs factors >>= simplify . mkProduct
evalAbs (Power' b (Number' n)) = do
  absBase <- evalAbs b
  absBase .**. mkNumber n
evalAbs I' = pure $ mkNumber 1
evalAbs (UnaryDiff' expr) = evalAbs expr
evalAbs (Quotient' n d) = do
  absN <- evalAbs n
  absD <- evalAbs d
  absN ./. absD
evalAbs (Abs' inner) = evalAbs inner
evalAbs expr = do
  linear <- linearForm expr "i"
  case linear of
    Just (LinearForm (unsimplify -> imag) (unsimplify -> real)) ->
      if imag /= mkNumber 0 && real /= mkNumber 0
        -- abs(a + b*i) = sqrt(a^2 + b^2)
        then simplify $ (imag ** 2 + real ** 2) ** (1 / 2)
        else return $ Abs' expr
    Nothing -> return $ Abs' expr

evalMax :: HS.HashSet SimplifiedExpr -> EvalResult SimplifiedExpr
evalMax exprSet = case HS.toList exprSet of
  [] -> throwError $ UnsupportedOperation "evalMax: empty set"
  [Max' xs] -> evalMax xs -- Flatten nested max
  [x] -> return x
  xs -> do
    flattened <- flattenMax xs
    let survivors = eliminateComparable flattened
    case survivors of
      [] ->
        throwError $
          UnsupportedOperation "evalMax: no survivors after elimination"
      [x] -> return x
      _ -> return $ mkMax (HS.fromList survivors)
  where
    -- Eliminate expressions that are definitely less than others
    eliminateComparable :: [SimplifiedExpr] -> [SimplifiedExpr]
    eliminateComparable = eliminateBy isDefinitelyGreaterThan

    -- -- Flatten nested Max expressions into a single list
    -- -- Max({3, Max({2, x})}) becomes [3, 2, x]
    flattenMax :: [SimplifiedExpr] -> EvalResult [SimplifiedExpr]
    flattenMax = flattenM $ \case
      Max' innerExprs -> pure $ Just (HS.toList innerExprs)
      _ -> pure Nothing

freeOf :: SimplifiedExpr -> SimplifiedExpr -> Bool
freeOf expr var
  | expr == var = False
  | isAtomic expr = True
  | otherwise = all (`freeOf` var) (operands expr)

operands :: Expr a -> [Expr a]
operands (Number' _) = []
operands (Fraction' _ _) = []
operands (Symbol' _) = []
operands (Product' xs) = NE.toList xs
operands (Sum' xs) = NE.toList xs
operands (Quotient' x y) = [x, y]
operands (Power' x y) = [x, y]
operands (Function' _ args) = NE.toList args
operands (Factorial' x) = [x]
operands (UnaryDiff' x) = [x]
operands (BinaryDiff' x y) = [x, y]

symbols :: SimplifiedExpr -> HS.HashSet Text
symbols expr = case expr of
  Number' _ -> HS.empty
  Fraction' _ _ -> HS.empty
  Symbol' s -> HS.singleton s
  Quotient' n d -> HS.union (symbols n) (symbols d)
  UnaryDiff' x -> symbols x
  BinaryDiff' x y -> HS.union (symbols x) (symbols y)
  Product' factors -> HS.unions $ NE.toList $ NE.map symbols factors
  Sum' terms -> HS.unions $ NE.toList $ NE.map symbols terms
  Power' b e -> HS.union (symbols b) (symbols e)
  Factorial' expr' -> symbols expr'
  Function' _ args -> HS.unions $ NE.toList $ NE.map symbols args

exponents :: SimplifiedExpr -> Text -> HS.HashSet SimplifiedExpr
exponents (Number' _) _ = HS.empty
exponents (Fraction' _ _) _ = HS.empty
exponents (Symbol' s) x =
  if s == x then HS.singleton (mkNumber 1) else HS.empty
exponents (Power' b e) x =
  if b == mkSymbol x
    then HS.union (HS.singleton e) (exponents e x)
    else exponents e x
exponents (Product' factors) x =
  HS.unions $ NE.toList $ NE.map (`exponents` x) factors
exponents (Sum' terms) x =
  HS.unions $ NE.toList $ NE.map (`exponents` x) terms
exponents (Quotient' n d) x =
  HS.union (exponents n x) (exponents d x)
exponents (UnaryDiff' expr) x =
  exponents expr x
exponents (BinaryDiff' expr1 expr2) x =
  HS.union (exponents expr1 x) (exponents expr2 x)
exponents (Factorial' expr) x =
  exponents expr x
exponents (Function' _ args) x =
  HS.unions $ NE.toList $ NE.map (`exponents` x) args

linearForm :: SimplifiedExpr -> Text -> EvalResult (Maybe LinearForm)
linearForm expr (mkSymbol -> x)
  | expr == x =
      pure $ Just $ LinearForm (mkNumber 1) (mkNumber 1)
  | isAtomic expr =
      pure $ Just $ LinearForm (mkNumber 0) expr
  | isProduct expr = analyseProduct expr x
  | isSum expr = analyseSum expr x
  | freeOf expr x =
      pure $ Just $ LinearForm (mkNumber 0) expr
  | otherwise = pure Nothing
  where
    analyseProduct :: SimplifiedExpr -> SimplifiedExpr -> EvalResult (Maybe LinearForm)
    analyseProduct u v
      | freeOf u v = pure $ Just $ LinearForm (mkNumber 0) u
      | otherwise = do
          q <- u ./. v
          if freeOf q v
            then pure $ Just $ LinearForm q (mkNumber 0)
            else pure Nothing

    analyseSum :: SimplifiedExpr -> SimplifiedExpr -> EvalResult (Maybe LinearForm)
    analyseSum (Sum' tss) (Symbol' v) = do
      let headT = NE.head tss
      restT <- simplify $ mkSum $ NE.fromList (NE.tail tss)
      fstL <- linearForm headT v
      rstL <- linearForm restT v
      case (fstL, rstL) of
        (Just (LinearForm f1 f2), Just (LinearForm r1 r2)) -> do
          newCoeff <- f1 .+. r1
          newConst <- f2 .+. r2
          pure $ Just $ LinearForm newCoeff newConst
        _ -> pure Nothing
    analyseSum _ _ =
      throwError $
        UnsupportedOperation
          "linearForm: analyseSum called with non-sum expression"

subs ::
  (Substitution.Pattern SimplifiedExpr, Substitution.Replacement SimplifiedExpr) ->
  SimplifiedExpr ->
  EvalResult SimplifiedExpr
subs
  (unsimplify . Substitution.unPattern -> pat, unsimplify . Substitution.unReplacement -> repl)
  (unsimplify -> expr) =
    simplify $
      Substitution.subs
        ( Substitution.Pattern pat,
          Substitution.Replacement repl
        )
        expr

seqSubs ::
  [(Substitution.Pattern SimplifiedExpr, Substitution.Replacement SimplifiedExpr)] ->
  SimplifiedExpr ->
  EvalResult SimplifiedExpr
seqSubs [] expr = pure expr
seqSubs ((p, r) : rest) expr = do
  result <- subs (p, r) expr
  seqSubs rest result

concurSubs ::
  [(Substitution.Pattern SimplifiedExpr, Substitution.Replacement SimplifiedExpr)] ->
  SimplifiedExpr ->
  EvalResult SimplifiedExpr
concurSubs equations (unsimplify -> expr) = do
  let structuralEquations =
        [ ( Substitution.Pattern (unsimplify $ Substitution.unPattern p),
            Substitution.Replacement (unsimplify $ Substitution.unReplacement r)
          )
          | (p, r) <- equations
        ]
  let result = Substitution.concurSubs structuralEquations expr
  simplify result
