module SymHask.Symbolic.Basic.Polynomial
  ( isMonomialSv,
    isPolynomialSv,
    degreeMonomialSv,
    degreeSv,
    coefficientSv,
    leadingCoefficientSv,
    isMonomialGpe,
    isPolynomialGpe,
    isRationalGre,
    rationalise,
    rationalVariables,
    variables,
    degreeGpe,
    coefficientGpe,
    leadingCoefficientGpe,
    coeffVarMonomial,
    collectTerms,
    algebraicExpand,
    expandMainOp,
    rationalExpand,
    denom,
    numer,
  )
where

import Control.Applicative ((<|>))
import Control.Monad (foldM)
import Control.Monad.Error.Class (MonadError (throwError))
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Maybe (catMaybes)
import Data.Text (Text)
import SymHask.Symbolic
import SymHask.Symbolic.Basic (freeOf, setFreeOf)
import SymHask.Symbolic.Basic.Utils (buildRestProduct, buildRestSum, eitherToMaybe, binomial)
import SymHask.Symbolic.Simplification ((.**.), (.*.), (.+.), (./.))

-- | Check whether an expression is a monomial in a single variable.
--
-- This follows the computational definition from the chapter:
-- constants, the variable itself, powers of the variable with integer
-- exponent greater than one, and products of monomials are monomials.
isMonomialSv :: SimplifiedExpr -> Text -> Bool
isMonomialSv (Number' _) _ = True
isMonomialSv (Fraction' _ _) _ = True
isMonomialSv (Symbol' s) x = s == x
isMonomialSv (Power' b (Number' e)) x = b == mkSymbol x && e > 1
isMonomialSv (Product' factors) x = all (`isMonomialSv` x) (NE.toList factors)
isMonomialSv _ _ = False

-- | Check whether an expression is a polynomial in a single variable.
--
-- A polynomial is either a monomial or a sum whose operands are all monomials.
isPolynomialSv :: SimplifiedExpr -> Text -> Bool
isPolynomialSv expr x =
  isMonomialSv expr x || case expr of
    Sum' terms -> all (`isMonomialSv` x) (NE.toList terms)
    _ -> False

-- | Compute the degree of a monomial in a single variable.
--
-- Returns the exponent of the variable if the expression is a monomial,
-- or Nothing (Undefined) if it is not.
--
-- Examples:
-- degreeMonomialSv (2*x^3) "x" = Just 3
-- degreeMonomialSv (3) "x" = Just 0
-- degreeMonomialSv (x+1) "x" = Nothing (not a monomial)
degreeMonomialSv :: SimplifiedExpr -> Text -> Maybe Integer
degreeMonomialSv expr x = snd <$> monomialSummary expr x

-- | Compute the degree of a polynomial in a single variable.
--
-- For a monomial, returns its degree.
-- For a sum of monomials, returns the maximum degree among all terms.
-- Returns Nothing (Undefined) if the expression is not polynomial in x.
--
-- Examples:
-- degreeSv (3*x^2 + 4*x + 5) "x" = Just 2
-- degreeSv (2*x^3) "x" = Just 3
-- degreeSv ((x+1)*(x+3)) "x" = Nothing (not a polynomial, product of sums)
-- degreeSv (3) "x" = Just 0
degreeSv :: SimplifiedExpr -> Text -> Maybe Integer
degreeSv expr x =
  degreeMonomialSv expr x <|> case expr of
    Sum' terms ->
      let degrees = [degreeMonomialSv term x | term <- NE.toList terms]
       in if Nothing `notElem` degrees
            then Just $ maximum (catMaybes degrees)
            else Nothing
    _ -> Nothing

-- | Compute the coefficient of x^j in a polynomial in a single variable.
--
-- Returns the corresponding coefficient if the expression is a polynomial in x,
-- 0 if j is larger than the degree.
-- Returns Left if the expression is not a polynomial in x.
coefficientSv :: SimplifiedExpr -> Text -> Integer -> EvalResult SimplifiedExpr
coefficientSv expr x j
  | not (isPolynomialSv expr x) =
      Left $
        UnsupportedOperation
          "coefficientSv: expression is not a polynomial"
  | otherwise = case expr of
      Sum' terms -> foldM addTerm (mkNumber 0) (NE.toList terms)
      _ -> coefficientMonomialSv expr x j
  where
    addTerm acc term = do
      coef <- coefficientMonomialSv term x j
      acc .+. coef

-- For a monomial of degree d, extract coefficient directly from the monomial summary.
coefficientMonomialSv :: SimplifiedExpr -> Text -> Integer -> EvalResult SimplifiedExpr
coefficientMonomialSv expr x j
  | not (isMonomialSv expr x) = pure $ mkNumber 0
  | j < 0 = pure $ mkNumber 0
  | otherwise = case monomialSummary expr x of
      Just (coeff, degree)
        | degree == j -> pure coeff
        | otherwise -> pure $ mkNumber 0
      Nothing -> pure $ mkNumber 0

-- | Compute the leading coefficient of a polynomial in a single variable.
--
-- If the expression is a polynomial in x, returns the coefficient of x^deg(u, x).
-- Otherwise returns an error.
leadingCoefficientSv :: SimplifiedExpr -> Text -> EvalResult SimplifiedExpr
leadingCoefficientSv expr x =
  case degreeSv expr x of
    Nothing ->
      Left $
        UnsupportedOperation
          "leadingCoefficientSv: expression is not a polynomial"
    Just degree ->
      case coefficientSv expr x degree of
        Left _ ->
          Left $
            UnsupportedOperation
              "leadingCoefficientSv: unable to compute leading coefficient"
        Right coeff -> pure coeff

-- | Extract (coefficient, degree) for a monomial in x.
--
-- Returns Just (coeff, deg) if the expression is a monomial in x,
-- where coeff is the coefficient and deg is the exponent of x.
-- For constants, deg = 0.
-- Returns Nothing if the expression is not a monomial.
monomialSummary :: SimplifiedExpr -> Text -> Maybe (SimplifiedExpr, Integer)
monomialSummary (Number' 0) _ = Nothing -- Zero is special (degree -∞)
monomialSummary (Number' n) _ = Just (mkNumber n, 0)
monomialSummary expr@(Fraction' _ _) _ = Just (expr, 0)
monomialSummary (Symbol' s) x
  | s == x = Just (mkNumber 1, 1)
  | otherwise = Nothing
monomialSummary (Power' b (Number' e)) x
  | b == mkSymbol x = Just (mkNumber 1, e)
  | otherwise = Nothing
monomialSummary (Product' (f1 :| [f2])) x = do
  (coeff1, deg1) <- monomialSummary f1 x
  (coeff2, deg2) <- monomialSummary f2 x
  coeff <- eitherToMaybe $ coeff1 .*. coeff2
  pure (coeff, deg1 + deg2)
monomialSummary _ _ = Nothing

-- | Check if an expression is a general monomial in a set of generalized variables.
--
-- A GME in S = {x₁, x₂, ..., xₘ} satisfies one of:
-- - GME-1: Free of all variables in S
-- - GME-2: u is a member of S
-- - GME-3: u = x^n where x ∈ S and n > 1 is an integer
-- - GME-4: u is a product where each operand is a GME in S
isMonomialGpe :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> Bool
isMonomialGpe u vars
  | HS.null vars = True
  | u `HS.member` vars = True -- GME-2: u is a generalized variable
  | otherwise = case u of
      Power' b (Number' e) ->
        -- GME-3: x^n where x in vars and n > 1
        (b `HS.member` vars && e > 1) || setFreeOf u (HS.toList vars)
      Product' factors ->
        all (`isMonomialGpe` vars) (NE.toList factors) -- GME-4: product of GMEs
      _ -> setFreeOf u (HS.toList vars) -- GME-1: free of all variables

-- | Check if an expression is a general polynomial in a set of generalized variables.
--
-- A GPE in S satisfies one of:
-- - GPE-1: u is a GME in S
-- - GPE-2: u is a sum where each operand is a GME in S
isPolynomialGpe :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> Bool
isPolynomialGpe u vars
  | u `HS.member` vars = True -- Short-circuit: u is itself a generalized variable (GME-2)
  | otherwise = case u of
      Sum' terms -> all (`isMonomialGpe` vars) (NE.toList terms) -- GPE-2
      _ -> isMonomialGpe u vars -- GPE-1

-- | Check whether an expression is a general rational expression (GRE)
-- in a set of generalized variables.
--
-- A GRE in S is an expression whose numerator and denominator are both
-- generalized polynomials in S.
isRationalGre :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> Bool
isRationalGre u vars =
  either (const False) (`isPolynomialGpe` vars) (numer u)
    && either (const False) (`isPolynomialGpe` vars) (denom u)

-- | Compute the natural set of generalized variables for a rational expression.
--
-- A rational variable set is the union of the variables in the numerator and
-- denominator of the expression.
rationalVariables :: SimplifiedExpr -> EvalResult (HS.HashSet SimplifiedExpr)
rationalVariables u = do
  n <- numer u
  d <- denom u
  pure $ variables n `HS.union` variables d

-- | Transform an algebraic expression into rationalized form.
--
-- This follows the recursive scheme from the text:
-- - powers are rationalized by rationalizing their base,
-- - products are rationalized operand-by-operand,
-- - sums are rationalized by combining operands over a common denominator.
rationalise :: SimplifiedExpr -> EvalResult SimplifiedExpr
rationalise u = case u of
  Power' base expn -> do
    base' <- rationalise base
    base' .**. expn
  Product' (f :| []) -> rationalise f
  Product' (f :| rest) -> do
    restProd <- buildRestProduct rest
    left <- rationalise f
    right <- rationalise restProd
    left .*. right
  Sum' (f :| []) -> rationalise f
  Sum' (f :| rest) -> do
    restSum <- buildRestSum rest
    g <- rationalise f
    r <- rationalise restSum
    rationaliseSum g r
  _ -> pure u

-- | Rationalize a sum of two already-rationalized expressions.
--
-- Uses the transformation m/r + n/s -> (m*s + n*r)/(r*s), and repeats
-- until both addends are denominator-free.
rationaliseSum :: SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
rationaliseSum u v = do
  m <- numer u
  r <- denom u
  n <- numer v
  s <- denom v
  if r == mkNumber 1 && s == mkNumber 1
    then u .+. v
    else do
      ms <- m .*. s
      nr <- n .*. r
      top <- ms .+. nr
      bot <- r .*. s
      merged <- top ./. bot
      rationalise merged

-- | Compute the natural set of generalized variables for an expression.
variables :: SimplifiedExpr -> HS.HashSet SimplifiedExpr
variables = \case
  Number' _ -> HS.empty -- VAR-1
  Fraction' _ _ -> HS.empty -- VAR-1
  Power' b (Number' e)
    | e > 1 -> HS.singleton b -- VAR-2 (integer exponent > 1)
  p@(Power' _ _) -> HS.singleton p -- VAR-2 otherwise: include the power itself
  Sum' terms -> foldMap variables (NE.toList terms) -- VAR-3
  Product' factors -> foldMap varForFactors (NE.toList factors) -- VAR-4
  expr -> HS.singleton expr -- VAR-5
  where
    varForFactors :: SimplifiedExpr -> HS.HashSet SimplifiedExpr
    varForFactors (Number' _) = HS.empty
    varForFactors (Fraction' _ _) = HS.empty
    varForFactors (Power' b (Number' e))
      | e > 1 = HS.singleton b
    varForFactors p@(Power' _ _) = HS.singleton p
    varForFactors s@(Sum' _) = HS.singleton s
    varForFactors factor = variables factor

-- | Degree for general polynomial expressions (GPE).
-- Returns Left if the expression is not a GPE in the given set of generalized variables.
-- Otherwise returns Right (Just n) for degree n, or Right Nothing to represent -∞ (zero polynomial).
degreeGpe :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> EvalResult (Maybe Integer)
degreeGpe u vars
  | not (isPolynomialGpe u vars) = Left $ UnsupportedOperation "degreeGpe: expression is not a GPE"
  | isMonomialGpe u vars = pure $ monomialGpeDegree u vars
  | otherwise = case u of
      Sum' terms -> do
        let ds = map (`monomialGpeDegree` vars) (NE.toList terms)
        if Nothing `elem` ds
          then pure Nothing
          else pure $ Just $ maximum (catMaybes ds)
      _ -> pure $ monomialGpeDegree u vars

-- | Compute degree of a monomial GME: sum of exponents of generalized variables.
-- Returns Nothing for the zero monomial.
monomialGpeDegree :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> Maybe Integer
monomialGpeDegree (Number' 0) _ = Nothing
monomialGpeDegree (Number' _) _ = Just 0
monomialGpeDegree (Fraction' _ _) _ = Just 0
monomialGpeDegree expr vars
  | expr `HS.member` vars = Just 1 -- expr itself is a generalized variable
  | otherwise = case expr of
      Symbol' _ -> Just 0 -- symbol not in vars
      Power' b (Number' e) ->
        if b `HS.member` vars && e > 1 then Just e else Just 0
      Product' factors -> do
        ds <- mapM (`monomialGpeDegree` vars) (NE.toList factors)
        return $ sum ds
      _ -> Just 0

-- | Extract (coefficient, degree) for a monomial w.r.t. a single generalized variable.
-- Returns Left when the operand is not a monomial in the generalized variable.
coefficientMonomialGpe :: SimplifiedExpr -> SimplifiedExpr -> EvalResult (SimplifiedExpr, Integer)
coefficientMonomialGpe u x
  | u == x = pure (mkNumber 1, 1)
  | otherwise = case u of
      Power' b (Number' e) -> handlePowerCase b e
      Product' factors -> foldM extractProductFactor (u, 0) factors
      _ -> handleDefaultCase
  where
    handlePowerCase b e
      | b == x && e > 1 = pure (mkNumber 1, e)
      | u `freeOf` x = pure (u, 0)
      | otherwise = Left $ UnsupportedOperation "coefficientMonomialGpe: not a monomial"

    extractProductFactor (coef, deg) factor = do
      (_, deg') <- coefficientMonomialGpe factor x
      if deg' == 0
        then pure (coef, deg) -- no update to coef or deg
        else do
          factorPower <- x .**. mkNumber deg'
          updatedCoef <- coef ./. factorPower
          pure (updatedCoef, deg')

    handleDefaultCase
      | u `freeOf` x = pure (u, 0)
      | otherwise = Left $ UnsupportedOperation "coefficientMonomialGpe: not a monomial"

-- | Coefficient_gpe(u, x, j): coefficient of x^j in polynomial u (generalized var x).
-- Returns Left if u is not a polynomial in x; otherwise returns the coefficient (possibly 0).
coefficientGpe :: SimplifiedExpr -> SimplifiedExpr -> Integer -> EvalResult SimplifiedExpr
coefficientGpe u x j
  | j < 0 = pure $ mkNumber 0
  | not (isPolynomialGpe u (HS.singleton x)) = Left $ UnsupportedOperation "coefficientGpe: expression is not a polynomial in x"
  | otherwise = case u of
      Sum' terms -> foldM addTerm (mkNumber 0) (NE.toList terms)
      _ -> do
        (c, m) <- coefficientMonomialGpe u x
        if m == j then pure c else pure $ mkNumber 0
  where
    addTerm acc term = do
      (c, m) <- coefficientMonomialGpe term x
      if m == j then acc .+. c else pure acc

-- | Leading_coefficient_gpe(u, x): leading coefficient of u with respect to
-- the generalized variable x. Returns Left when u is not a GPE in x.
leadingCoefficientGpe :: SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
leadingCoefficientGpe u x = do
  degM <- degreeGpe u (HS.singleton x)
  case degM of
    -- zero polynomial: leading coefficient is 0
    Nothing -> pure $ mkNumber 0
    Just d -> case coefficientGpe u x d of
      Left _ -> Left $ UnsupportedOperation "leadingCoefficientGpe: unable to compute leading coefficient"
      Right coeff -> pure coeff

-- | Extract coefficient and variable parts of a monomial w.r.t. a set of generalized variables.
-- Returns (coefficient, variable_part) where the monomial = coefficient * variable_part.
-- For a monomial that doesn't contain any variables in S, returns (monomial, 1).
coeffVarMonomial :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> EvalResult (SimplifiedExpr, SimplifiedExpr)
coeffVarMonomial u vars
  | HS.null vars = pure (u, mkNumber 1)
  | not $ isMonomialGpe u vars = Left $ UnsupportedOperation "coeffVarMonomial: expression is a monomial, not a product of coefficient and variable part"
  | setFreeOf u (HS.toList vars) = pure (u, mkNumber 1)
  | u `HS.member` vars = pure (mkNumber 1, u) -- u itself is a variable
  | otherwise = case u of
      Number' _ -> pure (u, mkNumber 1)
      Fraction' _ _ -> pure (u, mkNumber 1)
      Power' b (Number' e) ->
        if b `HS.member` vars && e > 1
          then pure (mkNumber 1, u) -- power of variable
          else pure (u, mkNumber 1)
      Product' factors -> decomposeProduct (NE.toList factors) vars
      _ -> pure (u, mkNumber 1)
  where
    decomposeProduct factors varSet = do
      pairs <- mapM (`coeffVarMonomial` varSet) factors
      let coeffs = map fst pairs
          varParts = map snd pairs
      coeff <- foldM (.*.) (mkNumber 1) coeffs
      varPart <- foldM (.*.) (mkNumber 1) varParts
      pure (coeff, varPart)

-- | Collect like terms in a general polynomial expression.
-- Returns the collected form of u, or Undefined (Left) if u is not a GPE in S.
-- In collected form, u is a GME in S or a sum of GMEs with distinct variable parts.
collectTerms :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> EvalResult SimplifiedExpr
collectTerms u vars
  | not (isPolynomialGpe u vars) =
      Left $ UnsupportedOperation "collectTerms: expression is not a GPE"
  | u `HS.member` vars = pure u -- already a single variable, which is a GME
  | otherwise = case u of
      Sum' terms -> collectFromSum (NE.toList terms) vars
      _ -> pure u -- already a single monomial, in collected form

-- | Helper to collect terms from a sum by grouping by variable part.
collectFromSum :: [SimplifiedExpr] -> HS.HashSet SimplifiedExpr -> EvalResult SimplifiedExpr
collectFromSum operands vars = do
  -- Extract coefficient and variable part for each operand
  pairs <- mapM (`coeffVarMonomial` vars) operands

  -- Fold into a hashmap keyed by variable part, summing coefficients
  let insertPair m (coef, varPart) =
        case HM.lookup varPart m of
          Nothing -> pure $ HM.insert varPart coef m
          Just existingCoef -> do
            summed <- existingCoef .+. coef
            pure $ HM.insert varPart summed m

  groupedMap <- foldM insertPair HM.empty pairs

  if HM.null groupedMap
    then pure $ mkNumber 0
    else do
      -- Build list of terms (coef * varPart) from the map
      termResults <- mapM (\(varPart, coef) -> coef .*. varPart) (HM.toList groupedMap)
      case NE.nonEmpty termResults of
        Nothing -> pure $ mkNumber 0
        Just termList -> simplify $ mkSum termList

-- | Algebraic_expand for integer-exponent case.
-- Expands sums, products and integer powers (n >= 2) recursively.
-- Macsyma-style extension (Properties 1 & 2):
--   1. Each complete sub-expression is in expanded form.
--   2. The denominator of each complete sub-expression is in expanded form.
-- Handles: function arguments are recursively expanded, and denominators
-- (represented as negative powers) are expanded and checked for zero.
algebraicExpand :: SimplifiedExpr -> EvalResult SimplifiedExpr
algebraicExpand u = do
  n <- numer u
  d <- denom u
  n' <- expandCore n
  d' <- expandCore d
  if d' == mkNumber 0
    then throwError DivisionByZero
    else
      if d' == mkNumber 1
        then pure n'
        else n' ./. d'

-- | Core structural expander used after numerator/denominator splitting.
-- This keeps the recursive expansion logic local to sums, products, powers,
-- and functions, while `algebraicExpand` handles quotient-like expressions by
-- splitting them first with `numer` and `denom`.
expandCore :: SimplifiedExpr -> EvalResult SimplifiedExpr
expandCore u = case u of
  Sum' (f :| []) -> pure f
  Sum' (f :| rest) -> do
    let first = f
    restSum <- buildRestSum rest
    left <- expandCore first
    right <- expandCore restSum
    left .+. right
  Product' (f :| []) -> pure f
  Product' (f :| rest) -> do
    let first = f
    restProd <- buildRestProduct rest
    r1 <- expandCore first
    r2 <- expandCore restProd
    expandProduct r1 r2
  Power' base (Number' n) | n >= 2 -> do
    b' <- expandCore base
    expandPower b' n
  Power' base (Fraction' num den)
    | num > 0 && den > 0 -> do
        b' <- expandCore base
        expandRationalPower b' num den
  Function' fname args -> do
    expandedArgs <- mapM expandCore (NE.toList args)
    case NE.nonEmpty expandedArgs of
      Just argList -> pure $ mkFunction fname argList
      Nothing -> pure u
  _ -> pure u

-- | Helper to recursively expand products and powers formed during expansion.
-- We only recurse when the expression still contains a genuinely expandable
-- sum or a power with an expandable base. This avoids re-entering on stable
-- products like x*y, which would otherwise loop forever.
tryExpand :: SimplifiedExpr -> EvalResult SimplifiedExpr
tryExpand expr
  | needsFurtherExpansion expr = expandCore expr
  | otherwise = pure expr
  where
    needsFurtherExpansion :: SimplifiedExpr -> Bool
    needsFurtherExpansion = \case
      Sum' _ -> True
      Product' factors -> any needsFurtherExpansion (NE.toList factors)
      Power' base (Number' n) -> n > 1 && not (isAtomic base) && needsFurtherExpansion base
      UnaryDiff' x -> needsFurtherExpansion x
      BinaryDiff' x y -> needsFurtherExpansion x || needsFurtherExpansion y
      Factorial' x -> needsFurtherExpansion x
      Function' _ args -> any needsFurtherExpansion (NE.toList args)
      _ -> False

-- | Expand_product as in pseudocode: expand product of two expanded expressions.
-- After computing the product, recursively expand any newly formed structures.
expandProduct :: SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
expandProduct (Sum' (f :| rest)) s = do
  rRem <- buildRestSum rest
  left <- expandProduct f s
  right <- expandProduct rRem s
  left .+. right
expandProduct r s@(Sum' (_ :| _)) = expandProduct s r
expandProduct r s = do
  prod <- r .*. s
  -- Recursively expand if the result contains unexpanded products or powers
  tryExpand prod

-- | Expand_power: expand (u)^n where n >= 2 and u is expanded.
-- After expansion, recursively expand any newly formed structures.
expandPower :: SimplifiedExpr -> Integer -> EvalResult SimplifiedExpr
expandPower u n
  | n <= 0 = pure $ mkNumber 1
  | n == 1 = pure u
  | otherwise = case u of
      Sum' (f :| rest) -> do
        r <- buildRestSum rest
        -- binomial-like expansion via recursion
        let ks = [0 .. n]
        terms <- mapM (expandTerm f r n) ks
        case NE.nonEmpty terms of
          Nothing -> pure $ mkNumber 0
          Just tlist -> do
            result <- simplify $ mkSum tlist
            -- Recursively expand the result in case it contains unexpanded products/powers
            tryExpand result
      _ -> do
        result <- simplify $ mkPower u (mkNumber n)
        -- Recursively expand if result is a product or power that might need expansion
        tryExpand result
  where
    -- expand term for a given k: c * f^(n-k) * Expand_power(r,k)
    expandTerm f r n' k = do
      let c = binomial n' k
      leftPow <- simplify $ mkPower f (mkNumber (n' - k))
      rightPow <- expandPower r k
      leftTerm <- mkNumber c .*. leftPow
      expandProduct leftTerm rightPow

-- | Expand a positive fractional power by splitting the exponent into its
-- integer part and fractional remainder:
--   u^(q + m) = u^m * u^q,  where  q = floor(f), m = f - floor(f).
expandRationalPower :: SimplifiedExpr -> Integer -> Integer -> EvalResult SimplifiedExpr
expandRationalPower u num den = do
  let (wholePart, remainder) = num `divMod` den
      fractionalPart = mkFraction remainder den

  wholeExpanded <-
    if wholePart <= 0
      then pure $ mkNumber 1
      else expandPower u wholePart

  if remainder == 0
    then pure wholeExpanded
    else do
      fractionalExpanded <- simplify $ mkPower u fractionalPart
      if wholeExpanded == mkNumber 1
        then pure fractionalExpanded
        else expandProduct fractionalExpanded wholeExpanded

-- Returns the numerator of an expression
numer :: SimplifiedExpr -> EvalResult SimplifiedExpr
numer (Fraction' n _) = pure $ mkNumber n
numer u@(Power' _ (Number' e)) =
  if e < 0 then pure $ mkNumber 1 else pure u
numer u@(Power' _ (Fraction' num _)) =
  if num < 0 then pure $ mkNumber 1 else pure u
numer (Product' (f :| rest)) = do
  fNum <- numer f
  rest' <- simplify . mkProduct . NE.fromList $ rest
  restNum <- numer rest'
  fNum .*. restNum
numer u = pure u

denom :: SimplifiedExpr -> EvalResult SimplifiedExpr
denom (Fraction' _ d) = pure $ mkNumber d
denom u@(Power' _ (Number' e)) =
  if e < 0
    then simplify $ mkPower u (mkNumber (-1))
    else pure $ mkNumber 1
denom u@(Power' _ (Fraction' num _)) =
  if num < 0
    then simplify $ mkPower u (mkNumber (-1))
    else pure $ mkNumber 1
denom (Product' (f :| rest)) = do
  fDenom <- denom f
  rest' <- simplify . mkProduct . NE.fromList $ rest
  restDenom <- denom rest'
  fDenom .*. restDenom
denom _ = pure $ mkNumber 1

-- | Transform an algebraic expression to rational-expanded form.
--
-- Steps:
-- 1. Rationalize the expression (bring to common denominators, etc.).
-- 2. Extract numerator and denominator with `numer` / `denom`.
-- 3. Algebraically expand numerator and denominator separately.
-- 4. Reassemble; if denominator expands to 0 return DivisionByZero.
rationalExpand :: SimplifiedExpr -> EvalResult SimplifiedExpr
rationalExpand = go
  where
    go expr = do
      next <- rationalExpandOnce expr
      if next == expr
        then pure next
        else go next

    rationalExpandOnce u = do
      -- Step 1: rationalise the whole expression
      r <- rationalise u
      -- Step 2: extract numerator and denominator
      n <- numer r
      d <- denom r
      -- Step 3: expand numerator and denominator
      n' <- algebraicExpand n
      d' <- algebraicExpand d
      -- Step 4: check denominator and reassemble
      if d' == mkNumber 0
        then throwError DivisionByZero
        else if d' == mkNumber 1
          then pure n'
          else n' ./. d'

-- | Expand only the main operator of an expression.
--
-- Sums are left unchanged. Products are distributed over immediate sum
-- operands, and powers with a positive integer exponent are expanded only
-- against the top-level sum in the base. Nested sums and powers are left
-- intact until a later pass expands them.
expandMainOp :: SimplifiedExpr -> EvalResult SimplifiedExpr
expandMainOp u@(Number' _) = pure u
expandMainOp u@(Fraction' _ _) = pure u
expandMainOp u@(Symbol' _) = pure u
expandMainOp u@(Sum' _) = pure u
expandMainOp (Product' factors) = expandMainProduct (NE.toList factors)
expandMainOp (Power' base (Number' n))
  | n >= 2 = expandMainPower base n
expandMainOp (Power' base (Fraction' num den))
  | num > 0 && den > 0 = expandMainRationalPower base num den
expandMainOp u = pure u

expandMainProduct :: [SimplifiedExpr] -> EvalResult SimplifiedExpr
expandMainProduct [] = pure $ mkNumber 1
expandMainProduct [x] = pure x
expandMainProduct [r, s] = expandMainProductPair r s
expandMainProduct (x : xs) = do
  rest <- expandMainProduct xs
  expandMainProductPair x rest

expandMainProductPair :: SimplifiedExpr -> SimplifiedExpr -> EvalResult SimplifiedExpr
expandMainProductPair (Sum' (f :| rest)) s = do
  r <- buildRestSum rest
  left <- expandMainProductPair f s
  right <- expandMainProductPair r s
  left .+. right
expandMainProductPair r (Sum' (f :| rest)) = do
  sRest <- buildRestSum rest
  left <- expandMainProductPair r f
  right <- expandMainProductPair r sRest
  left .+. right
expandMainProductPair r s = simplify $ mkProduct (r :| [s])

expandMainPower :: SimplifiedExpr -> Integer -> EvalResult SimplifiedExpr
expandMainPower u n
  | n <= 0 = pure $ mkNumber 1
  | n == 1 = pure u
  | otherwise = case u of
      Sum' (f :| rest) -> do
        r <- buildRestSum rest
        terms <- mapM (expandMainPowerTerm f r n) [0 .. n]
        case NE.nonEmpty terms of
          Nothing -> pure $ mkNumber 0
          Just tlist -> simplify $ mkSum tlist
      _ -> simplify $ mkPower u (mkNumber n)

expandMainPowerTerm :: SimplifiedExpr -> SimplifiedExpr -> Integer -> Integer -> EvalResult SimplifiedExpr
expandMainPowerTerm f r n' k = do
  let c = binomial n' k
  leftPow <- simplify $ mkPower f (mkNumber (n' - k))
  rightPow <- simplify $ mkPower r (mkNumber k)
  coeff <- mkNumber c .*. leftPow
  coeff .*. rightPow

expandMainRationalPower :: SimplifiedExpr -> Integer -> Integer -> EvalResult SimplifiedExpr
expandMainRationalPower u num den = do
  let (wholePart, remainder) = num `divMod` den
      fractionalPart = mkFraction remainder den

  wholeExpanded <-
    if wholePart <= 0
      then pure $ mkNumber 1
      else expandMainPower u wholePart

  if remainder == 0
    then pure wholeExpanded
    else do
      fractionalExpanded <- simplify $ mkPower u fractionalPart
      if wholeExpanded == mkNumber 1
        then pure fractionalExpanded
        else simplify $ mkProduct (fractionalExpanded :| [wholeExpanded])
