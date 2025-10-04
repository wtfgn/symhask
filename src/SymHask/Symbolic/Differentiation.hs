{-# LANGUAGE GADTs           #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PatternSynonyms #-}

module SymHask.Symbolic.Differentiation
    ( -- * Core types
      Derivative (..)
    , DiffVar (..)
      -- * Smart constructors (preferred interface)
    , dFun
    , dVar
    , derivative
    , nthDerivative
    , mixedDerivative
      -- * Conversion (for integration with other modules)
    , derivToExpr
    , diffVarToExpr
    , exprToDeriv
      -- * Main operations
    , computeDeriv
    , diff
    , implicitDiff
      -- * Analysis operations
    , derivOrderWrt
    , totalDerivOrder
    ) where

import           Control.Monad.Error.Class                               (throwError)
import qualified Data.List.NonEmpty                                      as NE
import           Data.Text                                               (Text)
import           SymHask.Symbolic
import           SymHask.Symbolic.Operators                              (freeOf,
                                                                          substitute)
import           SymHask.Symbolic.Simplification.AutomaticSimplification (automaticSimplify)

-- ============================================================================
-- * Data Types
-- ============================================================================

-- | Differentiation variables - only symbols and functions allowed
data DiffVar where
  Var :: Text -> DiffVar -- Variable like "x", "y"
  Fun :: Text -> NE.NonEmpty Expression -> DiffVar -- Function like f(x), g(x,y)
  deriving (Eq, Show)

-- | Derivative representation
data Derivative where
  -- | D expr [x, y, x] represents ∂³expr/∂x∂y∂x
  -- | D expr [x] represents ∂expr/∂x
  -- | D expr [] represents expr (no differentiation)
  D :: Expression -> [DiffVar] -> Derivative
  deriving (Eq, Show)

-- ============================================================================
-- * Smart Constructors
-- ============================================================================

-- Smart constructors with validation
dVar :: Text -> DiffVar
dVar = Var

dFun :: Text -> NE.NonEmpty Expression -> DiffVar
dFun = Fun

-- | Create simple derivative
derivative :: Expression -> DiffVar -> Derivative
derivative expr diffVar = D expr [diffVar]

-- | Create nth order derivative with respect to same variable
nthDerivative :: Expression -> DiffVar -> Int -> Derivative
nthDerivative expr diffVar n = D expr (replicate n diffVar)

-- | Create mixed partial derivative
mixedDerivative :: Expression -> [DiffVar] -> Derivative
mixedDerivative = D


-- ============================================================================
-- * Pattern Synonyms
-- ============================================================================


-- | Zero-order derivative (identity)
pattern ZeroD' :: Expression -> Derivative
pattern ZeroD' expr <- D expr [] where
  ZeroD' expr = D expr []

-- | First-order derivative
pattern FirstD' :: Expression -> DiffVar -> Derivative
pattern FirstD' expr var = D expr [var]


-- ============================================================================
-- * Conversion Functions
-- ============================================================================

-- | Convert DiffVar to Expression
diffVarToExpr :: DiffVar -> Expression
diffVarToExpr (Var s)          = Symbol s
diffVarToExpr (Fun fname args) = Function fname args

-- | Convert Derivative to Expression in Function form
derivToExpr :: Derivative -> Expression
derivToExpr (D expr []) = expr  -- No derivatives
derivToExpr (D expr vars) = Function "D" [expr, encodeVarList vars]
  where
    encodeVarList :: [DiffVar] -> Expression
    encodeVarList vs = Function "VarList" (NE.fromList (map diffVarToExpr vs))

-- | Parse Expression back to Derivative
exprToDeriv :: Expression -> Maybe Derivative
exprToDeriv = \case
  Function "D" [expr, Function "VarList" varExprs] -> do
    vars <- mapM parseVar varExprs
    return $ D expr (NE.toList vars)
  expr -> Just $ D expr []  -- Treat as zero-order derivative

parseVar :: Expression -> Maybe DiffVar
parseVar (Symbol s)            = Just (Var s)
parseVar (Function fname args) = return $ Fun fname args
parseVar _                     = Nothing

-- ============================================================================
-- * Clean Type-Safe Interface
-- ============================================================================

-- | Let u be an algebraic expression and let x be a symbol. The operator
-- diff(u, x), which evaluates the derivative of u with respect to x
--
-- Note: All derivatives of trigonometric and hyperbolic functions are expressed in terms of
-- of sin and cos, and sinh and cosh respectively.
--
-- Note: This function does not perform full simplification of the result.
-- It only applies automatic simplification before and after differentiation.
-- More advanced simplification techniques may be needed to fully simplify the
-- result.
-- For example:
-- @toHaskell <$> diff (mkFunction "cot" ["x"]) "x"@ gives you
-- @Right "(-1) * (sin x) ^ (-2)"@
-- but @toHaskell <$> diff (cos "x" / sin "x") "x" @ gives you
-- @Right "(-1) + (-1) * (cos x) ^ 2 * (sin x) ^ (-2)"@
-- In fact, they are semantically equivalent, but the latter is not fully simplified.
diff :: Expression -> Text -> ExpressionResult Expression
diff expr varName = do
  result <- computeDeriv (FirstD' expr (Var varName))
  return $ derivToExpr result

-- ============================================================================
-- * Core Differentiation Engine
-- ============================================================================
computeDeriv :: Derivative -> ExpressionResult Derivative
computeDeriv (D expr []) = return $ ZeroD' expr
computeDeriv (D expr [diffVar]) = do
  expr' <- automaticSimplify expr
  result <- applyDiffRule expr' diffVar
  simplified <- automaticSimplify result
  return $ ZeroD' simplified
computeDeriv (D expr (var : vars)) = do
  -- Apply first differentiation
  firstResult <- computeDeriv (FirstD' expr var)
  case firstResult of
    D resultExpr [] ->
      if null vars
        then return $ ZeroD' resultExpr
        else computeDeriv (D resultExpr vars)
    D _ _ -> throwError $ UnsupportedOperation "Unexpected derivative structure" expr

-- Quotient rule is not needed, it is simplfied to Product and Power
-- which are handled by diffProduct and diffPower respectively.
-- Assume u' is already simplified
applyDiffRule :: Expression -> DiffVar -> ExpressionResult Expression
applyDiffRule u' diffVar = case u' of
  _ | u' == diffVarToExpr diffVar       -> pure 1

  Power v w                             -> diffPower v w diffVar
  Sum terms                             -> diffSum terms diffVar
  Product factors                       -> diffProduct factors diffVar
  Function _ _                          -> diffFunction u' diffVar

  _ | freeOf u' (diffVarToExpr diffVar) -> pure 0

  _                                     -> pure $  derivToExpr (FirstD' u' diffVar)

-- Assume u' = (Power v w) is already simplified
diffPower :: Expression -> Expression -> DiffVar -> ExpressionResult Expression
diffPower v w diffVar = do
  dv <- differentiateWith v diffVar
  dw <- differentiateWith w diffVar
  return $ w * v ** (w - 1) * dv + dw * v ** w * log v


-- Assume u' = (Sum v w) is already simplified
-- Sum rule: (f₁ + f₂ + ... + fₙ)' = f₁' + f₂' + ... + fₙ'
diffSum :: Operands -> DiffVar -> ExpressionResult Expression
diffSum terms diffVar = do
  derivatives <- mapM (`differentiateWith` diffVar) terms
  return $ Sum derivatives


-- Assume u' = (Product factors) is already simplified
-- | Product rule: d/dx(Πfᵢ) = Σⱼ(dfⱼ/dx · Πᵢ≠ⱼfᵢ)
diffProduct :: NE.NonEmpty Expression -> DiffVar -> ExpressionResult Expression
diffProduct factors diffVar = do
  let factorList = NE.toList factors
  terms <- traverse (productTerm factorList diffVar) [0..length factorList - 1]
  pure $ sum $ filter (/= 0) terms
  where
    productTerm fs var i = do
      deriv <- applyDiffRule (fs !! i) var
      let others = take i fs <> drop (i + 1) fs
      pure $ deriv * product others

-- | Helper function for consistent differentiation
differentiateWith :: Expression -> DiffVar -> ExpressionResult Expression
differentiateWith = applyDiffRule

-- ============================================================================
-- * Function Differentiation (Known Functions)
-- ============================================================================

-- | Assume u' = f(v) is already simplified
-- Differentiate known functions using their derivatives and chain rule
diffFunction :: Expression -> DiffVar -> ExpressionResult Expression

-- Elementary functions with chain rule
diffFunction (Sqrt' v) x = do
  dv <- differentiateWith v x
  pure $ (1 / (2 * sqrt v)) * dv

diffFunction (Exp' v) x = do
  dv <- differentiateWith v x
  pure $ exp v * dv

diffFunction (LogBase' b v) x = do
  dv <- differentiateWith v x
  db <- differentiateWith b x
  pure $ dv / (v * log b) - db * log v / (b * log b ** 2)

diffFunction (Log' v) x = do
  dv <- differentiateWith v x
  pure $ dv / v

diffFunction (Sin' v) x = do
  dv <- differentiateWith v x
  pure $ cos v * dv

diffFunction (Cos' v) x = do
  dv <- differentiateWith v x
  pure $ - (sin v * dv)

diffFunction (Tan' v) x = do
  dv <- differentiateWith v x
  pure $ (1 / cos v) ** 2 * dv

diffFunction (Cot' v) x =do
  dv <- differentiateWith v x
  pure $ - ((1 / sin v) ** 2 * dv)

diffFunction (Sec' v) x = do
  dv <- differentiateWith v x
  pure (sin v / cos v ** 2 * dv)

diffFunction (Csc' v) x = do
  dv <- differentiateWith v x
  pure $ - (cos v / sin v ** 2 * dv)

diffFunction (Asin' v) x = do
  dv <- differentiateWith v x
  pure $ 1 / sqrt (1 - v ** 2) * dv

diffFunction (Acos' v) x = do
  dv <- differentiateWith v x
  pure $ - (1 / sqrt (1 - v ** 2) * dv)

diffFunction (Atan' v) x = do
  dv <- differentiateWith v x
  pure $ 1 / (1 + v ** 2) * dv

diffFunction (Acot' v) x = do
  dv <- differentiateWith v x
  pure $ - (1 / (1 + v ** 2) * dv)

diffFunction (Asec' v) x = do
  dv <- differentiateWith v x
  pure $ 1 / (abs v * sqrt (v ** 2 - 1)) * dv

diffFunction (Acsc' v) x = do
  dv <- differentiateWith v x
  pure $ - (1 / (abs v * sqrt (v ** 2 - 1)) * dv)

diffFunction (Sinh' v) x = do
  dv <- differentiateWith v x
  pure $ cosh v * dv

diffFunction (Cosh' v) x = do
  dv <- differentiateWith v x
  pure $ sinh v * dv

diffFunction (Tanh' v) x = do
  dv <- differentiateWith v x
  pure $ 1 / cosh v ** 2 * dv

diffFunction (Coth' v) x = do
  dv <- differentiateWith v x
  pure $ - (1 / sinh v ** 2 * dv)

diffFunction (Sech' v) x = do
  dv <- differentiateWith v x
  pure $ - (sinh v / cosh v ** 2 * dv)

diffFunction (Csch' v) x = do
  dv <- differentiateWith v x
  pure $ - (cosh v / sinh v ** 2 * dv)

diffFunction (Asinh' v) x = do
  dv <- differentiateWith v x
  pure $ 1 / sqrt (v ** 2 + 1) * dv

diffFunction (Acosh' v) x = do
  dv <- differentiateWith v x
  pure $ 1 / sqrt (v ** 2 - 1) * dv

diffFunction (Atanh' v) x = do
  dv <- differentiateWith v x
  pure $ 1 / (1 - v ** 2) * dv

diffFunction (ACoth' v) x = do
  dv <- differentiateWith v x
  pure $ 1 / (1 - v ** 2) * dv

diffFunction (ASech' v) x = do
  dv <- differentiateWith v x
  pure $ - (1 / (v * sqrt (1 - v ** 2)) * dv)

diffFunction (ACsch' v) x = do
  dv <- differentiateWith v x
  pure $ - (1 / (abs v * sqrt (1 + v ** 2)) * dv)

-- Unknown functions - apply generalized chain rule
-- d/dx f(u₁, u₂, ..., uₙ) = Σᵢ (∂f/∂uᵢ) * (duᵢ/dx)
diffFunction (Function fname args) diffVar = do
  chainTerms <- traverse (argTerm fname args diffVar) args
  return $ sum $ NE.filter (/= 0) chainTerms
  where
    argTerm funcName allArgs var arg = do
      argDiff <- applyDiffRule arg var
      if argDiff == 0
        then return 0
        else do
          argVar <- argToVar arg
          let partial = derivToExpr $ FirstD' (Function funcName allArgs) argVar
          return $ partial * argDiff

    -- Create appropriate DiffVar for function arguments
    argToVar :: Expression -> ExpressionResult DiffVar
    argToVar (Symbol s) = pure $ Var s
    argToVar (Function fname' args') = pure $ Fun fname' args'
     -- If the argument is neither a symbol nor a function, we cannot differentiate with respect to it
    argToVar expr = throwError $ UnsupportedOperation "Invalid function argument for differentiation" expr

diffFunction expr _ = throwError $
  UnsupportedOperation "Not a differentiable function" expr

-- ============================================================================
-- * Implicit Differentiation
-- ============================================================================

-- | Order of implicit derivative
newtype ImplicitOrder
  = Order Integer
  deriving (Eq, Ord, Show)


-- | Implicit differentiation by treating dependent variable as unknown function
implicitDiff
  :: (Expression, Expression)  -- ^ Equation (lhs, rhs)
  -> Text                      -- ^ Dependent variable (y), assumed to be a function of x
  -> Text                      -- ^ Independent variable (x)
  -> ExpressionResult Expression -- ^ Resulting d(lhs)/dx - d(rhs)/dx
implicitDiff (lhs, rhs) dependentVar independentVar = do
  -- Replace y with y(x) everywhere
  let mapping = \case
        Symbol var | var == dependentVar ->
          Just $ mkFunction dependentVar [Symbol independentVar]
        _ -> Nothing
  lhsImplicit <- substitute lhs mapping
  rhsImplicit <- substitute rhs mapping

  -- Now just differentiate normally - the chain rule will handle y(x) automatically!
  lhsDiff <- diff lhsImplicit independentVar
  rhsDiff <- diff rhsImplicit independentVar

  automaticSimplify $ lhsDiff - rhsDiff

-- ============================================================================
-- * Analysis Functions
-- ============================================================================

-- | Get derivative order with respect to a specific variable
derivOrderWrt :: Derivative -> DiffVar -> Integer
derivOrderWrt (D _ vars) targetVar =
  fromIntegral $ length $ filter (== targetVar) vars

totalDerivOrder :: Derivative -> Integer
totalDerivOrder (D _ vars) = fromIntegral $ length vars

-- -- | Get maximum derivative order with respect to a specific variable in an expression
-- -- Example:
-- -- let x = Symbol "x"
-- -- let yx = Function "y" [x]
-- -- let secDeriv = Function "D" (Function "y" [x] :| [Function "VarList" [x, x]])
-- -- let fstDeriv = Function "D" (Function "y" [x] :| [Function "VarList" [x]])
-- -- let expr = secDeriv + x*fstDeriv + 4*yx
-- -- maxDerivOrder expr (dVar "x") "y" == Just 2
-- maxDerivOrder :: Expression -> DiffVar -> Text -> Maybe Integer
-- maxDerivOrder expr targetVar funcName = do
--   derivs <- extractDerivs expr funcName
--   let orders = map (`derivOrder` targetVar) derivs
--   if null orders then Just 0 else Just (maximum orders)
--   where
--     extractDerivs :: Expression -> Text -> Maybe [Derivative]
--     extractDerivs (Sum terms) fname = concat <$> mapM (`extractDerivs` fname) terms
--     extractDerivs (Product factors) fname = concat <$> mapM (`extractDerivs` fname) factors
--     extractDerivs (Quotient n d) fname = do
--       numDerivs <- extractDerivs n fname
--       denomDerivs <- extractDerivs d fname
--       return $ numDerivs ++ denomDerivs
--     extractDerivs (UnaryDifference u) fname = extractDerivs u fname
--     extractDerivs (BinaryDifference l r) fname = do
--       leftDerivs <- extractDerivs l fname
--       rightDerivs <- extractDerivs r fname
--       return $ leftDerivs ++ rightDerivs
--     extractDerivs (Power b e) fname = do
--       baseDerivs <- extractDerivs b fname
--       expDerivs <- extractDerivs e fname
--       return $ baseDerivs ++ expDerivs
--     extractDerivs (Factorial u) fname = extractDerivs u fname
--     extractDerivs (Function "D" [e, Function "VarList" varExprs]) fname = do
--       vars <- mapM parseVar varExprs
--       return [D e (NE.toList vars) | containsFunc e fname]
--     extractDerivs _ _ = Just []

--     containsFunc :: Expression -> Text -> Bool
--     containsFunc (Symbol s) target = s == target
--     containsFunc (Product factors) target = any (`containsFunc` target) factors
--     containsFunc (Sum terms) target = any (`containsFunc` target) terms
--     containsFunc (Quotient n d) target = containsFunc n target || containsFunc d target
--     containsFunc (UnaryDifference u) target = containsFunc u target
--     containsFunc (BinaryDifference l r) target = containsFunc l target || containsFunc r target
--     containsFunc (Power b e) target = containsFunc b target || containsFunc e target
--     containsFunc (Function fname args) target =
--       fname == target || any (`containsFunc` target) args
--     containsFunc (Factorial u) target = containsFunc u target
--     containsFunc _ _ = False

