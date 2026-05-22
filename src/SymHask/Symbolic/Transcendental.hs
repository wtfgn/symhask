{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE MultiWayIf   #-}
{-# LANGUAGE ViewPatterns #-}

module SymHask.Symbolic.Transcendental
    ( contractExp
    , contractTrig
    , expandExp
    , expandTrig
    , separateSinCos
    , trigSubs
    ) where

import           Control.Monad                     (foldM, when)
import           Control.Monad.Error.Class         (throwError)
import           Data.List.NonEmpty                (NonEmpty ((:|)))
import qualified Data.List.NonEmpty                as NE
import           Math.Combinatorics.Exact.Binomial (choose)
import           SymHask.Symbolic
import           SymHask.Symbolic.Basic            (buildRestProduct,
                                                    buildRestSum, isZero,
                                                    mapOperands)
import           SymHask.Symbolic.Polynomial       (algebraicExpand, denom,
                                                    expandMainOp)
import           SymHask.Symbolic.Simplification   ((.**.), (.*.), (.+.), (.-.),
                                                    (./.))


-- | Expand expressions in the exponential sense.
--
-- The algorithm recursively expands subexpressions, then applies the
-- exponential rules to any exp(...) node:
--   exp(u + v) = exp(u) * exp(v)
--   exp(w * u) = exp(u) ^ w  when w is an integer
--
-- Before the exp rules are applied, the argument is algebraically expanded.
-- This lets expressions such as exp((x+y)(x-y)) reduce to exp(x^2) / exp(y^2).
-- If a denominator simplifies to 0 during the process, DivisionByZero is raised.
expandExp :: SimplifiedExpr -> Either ExprError SimplifiedExpr
expandExp expr = do
  d <- denom expr >>= expandExpCore
  when (isZero d) $ throwError DivisionByZero
  expandExpCore expr

expandExpCore :: SimplifiedExpr -> EvalResult SimplifiedExpr
expandExpCore u@(Number' _) = pure u
expandExpCore u@(Fraction' _ _) = pure u
expandExpCore u@(Symbol' _) = pure u
expandExpCore (Exp' x) =
  expandExpCore x >>= expandExpRules
expandExpCore u = mapOperands expandExpCore u

expandExpRules :: SimplifiedExpr -> EvalResult SimplifiedExpr
expandExpRules a = do
  a' <- algebraicExpand a
  case a' of
    Sum' (f :| rest) -> do
      r <- buildRestSum rest
      left <- expandExpRules f
      right <- expandExpRules r
      left .*. right
    Product' (f :| rest) -> do
      rest' <- buildRestProduct rest
      s <- expandExpRules rest'
      if isNumber f
        then s .**. f
        else return $ Exp' a'
    _ -> pure $ Exp' a'

data TrigKind
  = TrigSin
  | TrigCos

-- | Expand trigonometric functions sin/cos according to angle addition and multiple angle identities.
-- For non-sin/cos trig functions, use 'trigSubs' first to rewrite them in terms of sin/cos.
expandTrig :: SimplifiedExpr -> EvalResult SimplifiedExpr
expandTrig expr = do
  d <- denom expr >>= expandTrigCore
  when (isZero d) $ throwError DivisionByZero
  expandTrigCore expr >>= algebraicExpand

expandTrigCore :: SimplifiedExpr -> EvalResult SimplifiedExpr
expandTrigCore u@(Number' _)     = pure u
expandTrigCore u@(Fraction' _ _) = pure u
expandTrigCore u@(Symbol' _)     = pure u
expandTrigCore (Sin' x)          = expandTrigCore x >>= expandTrigRules TrigSin
expandTrigCore (Cos' x)          = expandTrigCore x >>= expandTrigRules TrigCos
expandTrigCore u                 = mapOperands expandTrigCore u

expandTrigRules :: TrigKind -> SimplifiedExpr -> EvalResult SimplifiedExpr
expandTrigRules kind arg = do
  arg' <- algebraicExpand arg
  case arg' of
    Sum' (f :| rest) -> do
      r <- buildRestSum rest
      expandTrigSum kind f r
    Product' (Number' n :| rest) -> do
      theta <- buildRestProduct rest
      expandTrigMultiple kind n theta
    _ -> pure $ mkTrig kind arg

expandTrigSum :: TrigKind -> SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
expandTrigSum TrigSin u v = do
  su <- expandTrigRules TrigSin u
  cu <- expandTrigRules TrigCos u
  sv <- expandTrigRules TrigSin v
  cv <- expandTrigRules TrigCos v
  left <- su .*. cv
  right <- cu .*. sv
  left .+. right
expandTrigSum TrigCos u v = do
  cu <- expandTrigRules TrigCos u
  cv <- expandTrigRules TrigCos v
  su <- expandTrigRules TrigSin u
  sv <- expandTrigRules TrigSin v
  left <- cu .*. cv
  right <- su .*. sv
  left .-. right

expandTrigMultiple :: TrigKind -> Integer -> SimplifiedExpr -> EvalResult SimplifiedExpr
expandTrigMultiple kind n theta
  | n == 0 = pure $ case kind of
      TrigSin -> mkNumber 0
      TrigCos -> mkNumber 1
  | n < 0 = do
      expanded <- expandTrigMultiple kind (-n) theta
      case kind of
        TrigSin -> simplify $ mkUnaryDiff expanded
        TrigCos -> pure expanded
  | n == 1 = expandTrigRules kind theta
  | otherwise = do
      -- Use the angle addition identity to reduce n recursively:
      -- sin(nθ) = sin((n-1)θ + θ) = sin((n-1)θ)*cos(θ) + cos((n-1)θ)*sin(θ)
      -- cos(nθ) = cos((n-1)θ + θ) = cos((n-1)θ)*cos(θ) - sin((n-1)θ)*sin(θ)
      su <- expandTrigMultiple TrigSin (n - 1) theta
      cu <- expandTrigMultiple TrigCos (n - 1) theta
      sv <- expandTrigRules TrigSin theta
      cv <- expandTrigRules TrigCos theta
      case kind of
        TrigSin -> do
          left <- su .*. cv
          right <- cu .*. sv
          left .+. right
        TrigCos -> do
          left <- cu .*. cv
          right <- su .*. sv
          left .-. right

mkTrig :: TrigKind -> SimplifiedExpr -> SimplifiedExpr
mkTrig TrigSin = Sin'
mkTrig TrigCos = Cos'

-- | Contract exponential expressions by combining products of exponentials and
-- rewriting powers of exponentials into a single exponential.
contractExp :: SimplifiedExpr -> EvalResult SimplifiedExpr
contractExp u@(Number' _)     = pure u
contractExp u@(Fraction' _ _) = pure u
contractExp u@(Symbol' _)     = pure u
contractExp u                 = mapOperands contractExp u >>= contractExpRules

contractExpRules :: SimplifiedExpr -> EvalResult SimplifiedExpr
contractExpRules u = do
  v <- expandMainOp u
  case v of
    Power' (Exp' x) s -> do
      p <- x .*. s
      contracted <- if needsFurtherContraction p then contractExpRules p else return p
      pure $ Exp' contracted
    Product' factors -> do
      (p, s) <- foldM combineExpFactors (mkNumber 1, mkNumber 0) factors
      if isZero s then return v else Exp' s .*. p
    Sum' terms -> foldM combineExpTerms (mkNumber 0) terms
    _ -> pure v
  where
    needsFurtherContraction expr = isProduct expr || isPower expr

    combineExpFactors (p, s) factor = case factor of
      Exp' n -> do
        s' <- s .+. n
        return (p, s')
      _ -> do
        p' <- p .*. factor
        return (p', s)

    combineExpTerms acc term
      | isProduct term || isPower term = contractExpRules term >>= (acc .+.)
      | otherwise = acc .+. term

-- | Separate an expression into a non-trig part and a sin/cos part.
--
-- Returns a pair (r, s) where:
-- - s is the product of sin/cos operands and positive integer powers of sin/cos
-- - r is the product of the remaining operands
-- For non-product expressions:
-- - if expression is sin/cos or a positive integer power of sin/cos, returns (1, expr)
-- - otherwise returns (expr, 1)
separateSinCos :: SimplifiedExpr -> EvalResult (SimplifiedExpr, SimplifiedExpr)
separateSinCos expr = case expr of
  Product' factors -> do
    let (trigFactors, restFactors) = foldr splitFactor ([], []) (NE.toList factors)
    r <- buildProductOrOne restFactors
    s <- buildProductOrOne trigFactors
    pure (r, s)
  _
    | isSinCosLike expr -> pure (mkNumber 1, expr)
    | otherwise -> pure (expr, mkNumber 1)
  where
    splitFactor factor (trigs, rests)
      | isSinCosLike factor = (factor : trigs, rests)
      | otherwise = (trigs, factor : rests)

    isSinCosLike = \case
      Sin' _ -> True
      Cos' _ -> True
      Power' base (Number' n)
        | n > 0 -> case base of
            Sin' _ -> True
            Cos' _ -> True
            _      -> False
      _ -> False

    buildProductOrOne []  = pure $ mkNumber 1
    buildProductOrOne [u] = pure u
    buildProductOrOne us  = simplify $ mkProduct (NE.fromList us)

-- | Contract trigonometric expressions by combining products and powers of sin/cos.
--
-- The algorithm applies three product-to-sum identities:
--   sin(θ)sin(φ) = cos(θ-φ)/2 - cos(θ+φ)/2    (7.30)
--   cos(θ)cos(φ) = cos(θ+φ)/2 + cos(θ-φ)/2    (7.31)
--   sin(θ)cos(φ) = sin(θ+φ)/2 + sin(θ-φ)/2    (7.32)
--
-- It also contracts powers of sin and cos using formulas (7.35) and (7.36).
-- An expression is in trigonometric-contracted form when:
--   1. Each product has at most one sin/cos operand
--   2. No power has a sin/cos base with positive integer exponent
--   3. Each complete sub-expression is algebraically expanded
contractTrig :: SimplifiedExpr -> EvalResult SimplifiedExpr
contractTrig u@(Number' _) = pure u
contractTrig u@(Fraction' _ _) = pure u
contractTrig u@(Symbol' _) = pure u
contractTrig u = mapOperands contractTrig u >>= contractTrigRules

contractTrigRules :: SimplifiedExpr -> EvalResult SimplifiedExpr
contractTrigRules u = do
  v <- expandMainOp u
  case v of
    Power' _ _ -> contractTrigPower v
    Product' _ -> do
      (c, d) <- separateSinCos v
      if
        | d == mkNumber 1 -> return v
        | isSinCos d -> return v
        | isPower d -> contractTrigPower d >>= (c .*.) >>= contractTrigRules
        | otherwise -> contractTrigProduct d >>= (c .*.) >>= contractTrigRules
    Sum' terms -> foldM contractSumTerm (mkNumber 0) (NE.toList terms)
    _ -> pure v
  where
    contractSumTerm acc term = do
      contracted <-
        if isProduct term || isPower term
          then contractTrigRules term
          else pure term
      acc .+. contracted

contractTrigProduct :: SimplifiedExpr -> EvalResult SimplifiedExpr
contractTrigProduct u@(Product' (_ :| [])) = pure u
contractTrigProduct (Product' (a :| [b])) = contractProductPair a b
contractTrigProduct (Product' (a :| as)) = do
  rest <- buildRestProduct as
  b <- contractTrigProduct rest
  a .*. b >>= contractExpRules
contractTrigProduct expr = pure expr

contractProductPair :: SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
contractProductPair a@(Power' _ _) b = do
  a' <- contractTrigPower a
  a' .*. b >>= contractTrigPower
contractProductPair a b@(Power' _ _) = do
  b' <- contractTrigPower b
  a .*. b' >>= contractTrigPower
contractProductPair a b = applyProductIdentity a b

applyProductIdentity :: SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
applyProductIdentity (Sin' x) (Sin' y) = do
  -- Algebraic expansion is needed to ensure the arguments
  -- are in the correct form for the identity to apply.
  -- For example, x = x/2 + y/2, and y = x/2 - y/2,
  -- sin(x)*cos(y) -> sin(x/2 + y/2)*cos(x/2 - y/2) should contract to sin(x)/2 + sin(y)/2,
  -- not sin((x/2 + y/2) + (x/2 - y/2))/2 + sin((x/2 + y/2) - (x/2 - y/2))/2
  -- sin(x)sin(y) = cos(x-y)/2 - cos(x+y)/2
  (unsimplify -> xMinusY) <- x .-. y >>= algebraicExpand
  (unsimplify -> xPlusY) <- x .+. y >>= algebraicExpand
  simplify $ cos xMinusY / 2 - cos xPlusY / 2
applyProductIdentity (Cos' x) (Cos' y) = do
  -- cos(x)cos(y) = cos(x+y)/2 + cos(x-y)/2
  (unsimplify -> xPlusY) <- x .+. y >>= algebraicExpand
  (unsimplify -> xMinusY) <- x .-. y >>= algebraicExpand
  simplify $ cos xPlusY / 2 + cos xMinusY / 2
applyProductIdentity (Cos' x) (Sin' y) = do
  -- cos(x)sin(y) = sin(x+y)/2 + sin(y-x)/2
  (unsimplify -> xPlusY) <- x .+. y >>= algebraicExpand
  (unsimplify -> yMinusX) <- y .-. x >>= algebraicExpand
  simplify $ sin xPlusY / 2 + sin yMinusX / 2
applyProductIdentity (Sin' x) (Cos' y) = do
  -- sin(x)cos(y) = sin(x+y)/2 + sin(x-y)/2
  (unsimplify -> xPlusY) <- x .+. y >>= algebraicExpand
  (unsimplify -> xMinusY) <- x .-. y >>= algebraicExpand
  simplify $ sin xPlusY / 2 + sin xMinusY / 2
applyProductIdentity _ _ =
  throwError $
    UnsupportedOperation
      "Only products of sin/cos can be contracted using product-to-sum identities."

contractTrigPower :: SimplifiedExpr -> EvalResult SimplifiedExpr
contractTrigPower (Power' (Sin' theta) (Number' n))
  | n > 1 =
      contractSinPower theta n
contractTrigPower (Power' (Cos' theta) (Number' n))
  | n > 1 =
      contractCosPower theta n
contractTrigPower expr = pure expr

contractSinPower :: SimplifiedExpr -> Integer -> EvalResult SimplifiedExpr
contractSinPower theta n
  | even n = do
      -- For even n: formula 7.36
      let m = n `div` 2
      let multiplier = (-1) ^ m
      -- Constant term: C(n, n/2) / 2^n (no multiplier here)
      constTerm <- mkNumber (choose n m) ./. mkNumber (2 ^ n)
      -- Rest sum with (-1)^(n/2) multiplier
      let restTerms = [0 .. m - 1]
      restSum <-
        foldM
          ( \acc j -> do
              let coeff = multiplier * (-1) ^ j * choose n j
              let arg = mkNumber (n - 2 * j) .*. theta
              arg' <- arg
              let cosArg = mkFunction "cos" (arg' :| [])
              coefTerm <- mkNumber coeff ./. mkNumber (2 ^ (n - 1))
              term <- coefTerm .*. cosArg
              acc .+. term
          )
          (mkNumber 0)
          restTerms
      constTerm .+. restSum
  | otherwise = do
      -- For odd n: formula 7.36
      let m = (n - 1) `div` 2
      let sign = (-1) ^ ((n - 1) `div` 2)
      let restTerms = [0 .. m]
      foldM
        ( \acc j -> do
            let coeff = sign * (-1) ^ j * choose n j
            let arg = mkNumber (n - 2 * j) .*. theta
            arg' <- arg
            let sinArg = mkFunction "sin" (arg' :| [])
            temp <- mkNumber coeff ./. mkNumber (2 ^ (n - 1))
            term <- temp .*. sinArg
            acc .+. term
        )
        (mkNumber 0)
        restTerms

contractCosPower :: SimplifiedExpr -> Integer -> EvalResult SimplifiedExpr
contractCosPower theta n
  | even n = do
      -- For even n: formula 7.35
      let m = n `div` 2
      let term1 = mkNumber (choose n m) ./. mkNumber (2 ^ n)
      term1' <- term1
      let restTerms = [0 .. m - 1]
      restSum <-
        foldM
          ( \acc j -> do
              let coeff = choose n j
              let arg = mkNumber (n - 2 * j) .*. theta
              arg' <- arg
              let cosArg = mkFunction "cos" (arg' :| [])
              temp <- mkNumber coeff ./. mkNumber (2 ^ (n - 1))
              term <- temp .*. cosArg
              acc .+. term
          )
          (mkNumber 0)
          restTerms
      term1' .+. restSum
  | otherwise = do
      -- For odd n: formula 7.35
      let m = (n - 1) `div` 2
      let restTerms = [0 .. m]
      foldM
        ( \acc j -> do
            let coeff = choose n j
            let arg = mkNumber (n - 2 * j) .*. theta
            arg' <- arg
            let cosArg = mkFunction "cos" (arg' :| [])
            temp <- mkNumber coeff ./. mkNumber (2 ^ (n - 1))
            term <- temp .*. cosArg
            acc .+. term
        )
        (mkNumber 0)
        restTerms

isSinCos :: SimplifiedExpr -> Bool
isSinCos (Sin' _) = True
isSinCos (Cos' _) = True
isSinCos _        = False

-- | Substitute trigonometric functions tan/cot/sec/csc with sin/cos representations.
--
-- tan(u) = sin(u) / cos(u)
-- cot(u) = cos(u) / sin(u)
-- sec(u) = 1 / cos(u)
-- csc(u) = 1 / sin(u)
trigSubs :: SimplifiedExpr -> EvalResult SimplifiedExpr
trigSubs u@(Number' _) = pure u
trigSubs u@(Fraction' _ _) = pure u
trigSubs u@(Symbol' _) = pure u
trigSubs (Tan' x) = do
  x' <- trigSubs x
  let sinx = mkFunction "sin" (x' :| [])
      cosx = mkFunction "cos" (x' :| [])
  simplify $ mkQuotient sinx cosx
trigSubs (Cot' x) = do
  x' <- trigSubs x
  let sinx = mkFunction "sin" (x' :| [])
      cosx = mkFunction "cos" (x' :| [])
  simplify $ mkQuotient cosx sinx
trigSubs (Sec' x) = do
  x' <- trigSubs x
  let cosx = mkFunction "cos" (x' :| [])
  simplify $ mkQuotient (mkNumber 1) cosx
trigSubs (Csc' x) = do
  x' <- trigSubs x
  let sinx = mkFunction "sin" (x' :| [])
  simplify $ mkQuotient (mkNumber 1) sinx
trigSubs u = mapOperands trigSubs u

-- | Simplify trigonometric expressions by applying expansion and contraction rules.
-- Returns an algebraic expression in trigonometric-contracted form.
-- simplifyTrig :: SimplifiedExpr -> EvalResult SimplifiedExpr
-- simplifyTrig u = do
--   w <- trigSubs u >>= rationalise
--   n <- numer w >>= expandTrig >>= contractTrig
--   d <- denom w >>= expandTrig >>= contractTrig
--   when (isZero d) $ throwError DivisionByZero
--   n ./. d
