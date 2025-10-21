{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}

module SymHask.Symbolic.Analysis
    ( FunctionParity (..)
    , LinearForm (..)
    , allFreeOf
    , completeSubExprs
    , containParameters
    , evenOdd
    , freeOf
    , isNumerical
    , linearForm
    , maxExpr
    , mkMax
    , pattern Max'
    , symbols
    , treeSize
    , maxExponent
    , collectExponents
    , absExpr
    , separateFactors
    ) where

import           Control.Monad
import           Control.Monad.Error.Class
import qualified Data.HashSet                                    as HS
import qualified Data.List.NonEmpty                              as NE
import           Data.Text                                       (Text)
import           SymHask.Core.Expression
import           SymHask.Symbolic.Manipulation.Substitution
import           SymHask.Symbolic.Simplification


completeSubExprs :: SimplifiedExpr -> HS.HashSet SimplifiedExpr
completeSubExprs expr
  | null operands = HS.singleton expr
  | otherwise     = HS.insert expr (HS.unions subSets)
  where
    operands = getOperands expr
    subSets  = map completeSubExprs operands

freeOf :: SimplifiedExpr -> SimplifiedExpr -> Bool
freeOf expr var
  | expr == var = False
  | isAtomic expr = True
  | otherwise = all (`freeOf` var) (getOperands expr)

allFreeOf :: (Foldable f) => SimplifiedExpr -> f SimplifiedExpr -> Bool
allFreeOf var = all (`freeOf` var)

data FunctionParity
  = EvenFunc
  | OddFunc
  | NeitherFunc
  deriving (Eq, Show)


evenOdd :: SimplifiedExpr -> Text -> EvalResult FunctionParity
evenOdd expr x = do
  negX <- simplify (negate (mkSymbol x) :: UnsimplifiedExpr)
  substituted <- subs
    (Pattern (mkSymbol x), Replacement negX)
    expr
  if
    | expr .-. substituted == pure (mkNumber 0) -> return EvenFunc
    | expr .+. substituted == pure (mkNumber 0) -> return OddFunc
    | otherwise                                  -> return NeitherFunc

-- | A linear form represented as a*x + b
data LinearForm
  = LinearForm
      { coeffTerm :: SimplifiedExpr
        -- Coefficient of x
      , constTerm :: SimplifiedExpr
        -- Constant term
      }
  deriving (Eq, Show)


linearForm :: SimplifiedExpr -> Text -> EvalResult (Maybe LinearForm)
linearForm expr (mkSymbol -> x)
  | expr == x =
    pure $ Just $ LinearForm (mkNumber 1) (mkNumber 1)
  | isAtomic expr =
    pure $ Just $ LinearForm (mkNumber 0) expr
  | isProduct expr = analyseProduct expr x
  | isSum expr     = analyseSum expr x
  | freeOf expr x =
    pure $ Just $ LinearForm (mkNumber 0) expr
  | otherwise     = pure Nothing
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
        _                    -> pure Nothing
    analyseSum _ _ = throwError $ UnsupportedOperation
      "linearForm: analyseSum called with non-sum expression"

symbols :: SimplifiedExpr -> HS.HashSet Text
symbols expr = case expr of
  Number' _        -> HS.empty
  Fraction' _ _    -> HS.empty
  Symbol' s        -> HS.singleton s
  Quotient' n d    -> HS.union (symbols n) (symbols d)
  UnaryDiff' x     -> symbols x
  BinaryDiff' x y  -> HS.union (symbols x) (symbols y)
  Product' factors -> HS.unions $ NE.toList $ NE.map symbols factors
  Sum' terms       -> HS.unions $ NE.toList $ NE.map symbols terms
  Power' b e       -> HS.union (symbols b) (symbols e)
  Factorial' expr' -> symbols expr'
  Function' _ args -> HS.unions $ NE.toList $ NE.map symbols args



containParameters :: SimplifiedExpr -> Text -> Bool
containParameters simplified param =
  HS.member param (symbols simplified)

isNumerical :: SimplifiedExpr -> Bool
isNumerical = \case
  Number' _     -> True
  Fraction' _ _ -> True
  Pi'         -> True
  E'         -> True
  Symbol' _     -> False
  Quotient' n d  -> isNumerical n && isNumerical d
  UnaryDiff' x   -> isNumerical x
  BinaryDiff' x y -> isNumerical x && isNumerical y
  Product' factors    -> all isNumerical factors
  Sum' terms        -> all isNumerical terms
  Power' b e -> isNumerical b && isNumerical e
  Factorial' expr  -> isNumerical expr
  Function' _ args -> all isNumerical args

treeSize :: SimplifiedExpr -> Int
treeSize = \case
  Number' _     -> 1
  Fraction' _ _ -> 3
  Symbol' _     -> 1
  Quotient' n d  -> 1 + treeSize n + treeSize d
  UnaryDiff' x   -> 1 + treeSize x
  BinaryDiff' x y -> 1 + treeSize x + treeSize y
  Product' factors    -> 1 + sum (NE.map treeSize factors)
  Sum' terms        -> 1 + sum (NE.map treeSize terms)
  Power' b e -> 1 + treeSize b + treeSize e
  Factorial' expr  -> 1 + treeSize expr
  Function' _ args -> 1 + sum (NE.map treeSize args)




pattern Max' :: HS.HashSet SimplifiedExpr -> SimplifiedExpr
pattern Max' exprSet <- Function' "max" (NE.toList -> (HS.fromList -> exprSet))


mkMax :: HS.HashSet SimplifiedExpr -> SimplifiedExpr
mkMax exprSet = mkFunction "max" (NE.fromList (HS.toList exprSet))


maxExpr :: HS.HashSet SimplifiedExpr -> EvalResult SimplifiedExpr
maxExpr exprSet = case HS.toList exprSet of
  [] -> throwError $ UnsupportedOperation "maxExpr: empty set"
  [Max' xs] -> maxExpr xs  -- Flatten nested max
  [x] -> return x
  xs -> do
    flattened <- flattenMax xs
     -- Now eliminate comparable expressions
     -- First, simplify all expressions
    let survivors = eliminateComparable flattened
    case survivors of
      []  -> throwError $
        UnsupportedOperation "maxExpr: no survivors after elimination"
      [x] -> return x
      _   -> return $ mkMax (HS.fromList survivors)
 where
    -- Eliminate expressions that are definitely less than others
    eliminateComparable :: [SimplifiedExpr] -> [SimplifiedExpr]
    eliminateComparable [] = []
    eliminateComparable [x] = [x]
    eliminateComparable (x:xs) =
      if any (`isDefinitelyGreaterThan` x) xs  -- Check if anything in xs dominates x
      then eliminateComparable xs            -- x is eliminated, continue without it
      else x : eliminateComparable (filter (not . isDefinitelyGreaterThan x) xs)
          -- x survives, eliminate anything x dominates, continue recursively

    -- -- Flatten nested Max expressions into a single list
    -- -- Max({3, Max({2, x})}) becomes [3, 2, x]
    flattenMax :: [SimplifiedExpr] -> EvalResult [SimplifiedExpr]
    flattenMax = foldM flattenSingle []
      where
        flattenSingle :: [SimplifiedExpr] -> SimplifiedExpr -> EvalResult [SimplifiedExpr]
        flattenSingle acc (Max' innerExprs) = do
          -- Recursively flatten the inner Max expressions
          innerFlattened <- flattenMax (HS.toList innerExprs)
          return $ acc ++ innerFlattened
        flattenSingle acc expr = return $ acc ++ [expr]


    isDefinitelyGreaterThan :: SimplifiedExpr -> SimplifiedExpr -> Bool
    isDefinitelyGreaterThan a b = case a .-. b of
      Right (Number' n)         -> n > 0
      Right (Fraction' num den) -> num > 0 && den > 0
      -- If simplification fails or not a clear number,
      -- assume not definitely greater
      _                         -> False

maxExponent :: SimplifiedExpr -> Text -> EvalResult SimplifiedExpr
maxExponent expr x = maxExpr $ collectExponents expr x

collectExponents :: SimplifiedExpr -> Text -> HS.HashSet SimplifiedExpr
collectExponents (Number' _) _ = HS.empty
collectExponents (Fraction' _ _) _ = HS.empty
collectExponents (Symbol' s) x =
  if s == x then HS.singleton (mkNumber 1) else HS.empty
collectExponents (Power' b e) x =
  if b == mkSymbol x
    then HS.union (HS.singleton e) (collectExponents e x)
    else collectExponents e x
collectExponents (Product' factors) x =
  HS.unions $ NE.toList $ NE.map (`collectExponents` x) factors
collectExponents (Sum' terms) x =
  HS.unions $ NE.toList $ NE.map (`collectExponents` x) terms
collectExponents (Quotient' n d) x =
  HS.union (collectExponents n x) (collectExponents d x)
collectExponents (UnaryDiff' expr) x =
  collectExponents expr x
collectExponents (BinaryDiff' expr1 expr2) x =
  HS.union (collectExponents expr1 x) (collectExponents expr2 x)
collectExponents (Factorial' expr) x =
  collectExponents expr x
collectExponents (Function' _ args) x =
  HS.unions $ NE.toList $ NE.map (`collectExponents` x) args

absExpr :: SimplifiedExpr -> EvalResult SimplifiedExpr
absExpr (Number' n) = pure $ mkNumber (abs n)
absExpr (Fraction' n d) = simplify $ mkFraction (abs n) (abs d)
absExpr (Product' factors) = mapM absExpr factors >>= simplify . mkProduct
absExpr (Power' b (Number' n)) = do
  absBase <- absExpr b
  absBase .**. mkNumber n
absExpr I' = pure $ mkNumber 1
absExpr (UnaryDiff' expr) = absExpr expr
absExpr (Quotient' n d) = do
  absN <- absExpr n
  absD <- absExpr d
  absN ./. absD
absExpr (Abs' inner) = absExpr inner
absExpr expr = do
  linear <- linearForm expr "i"
  case linear of
    Just (LinearForm imag real) ->
      if imag /= mkNumber 0 && real /= mkNumber 0
      -- abs(a + b*i) = sqrt(a^2 + b^2)
      then do
        imagSq <- imag .**. mkNumber 2
        realSq <- real .**. mkNumber 2
        sumSq <- imagSq .+. realSq
        half <- simplify $ mkFraction 1 2
        sumSq .**. half
      else return $ Abs' expr
    Nothing -> return $ Abs' expr

-- | Separate factors into parts free of variable x and parts dependent on x
-- For expression u*v*w..., separates into (free_part, dependent_part) where:
-- - free_part contains factors that don't depend on x
-- - dependent_part contains factors that do depend on x
separateFactors :: SimplifiedExpr -> SimplifiedExpr -> EvalResult (SimplifiedExpr, SimplifiedExpr)
separateFactors (Product' factors) var =
  foldM processFactor (mkNumber 1, mkNumber 1) (NE.toList factors)
  where
    -- Process a single factor
    processFactor
      :: (SimplifiedExpr, SimplifiedExpr)
      -> SimplifiedExpr
      -> EvalResult (SimplifiedExpr, SimplifiedExpr)
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


