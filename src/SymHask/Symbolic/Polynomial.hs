-- |
-- Module: SymHask.Symbolic.Basic.Polynomial
-- Description: Operations on polynomials and monomials
-- Copyright: Copyright 2026 wtfgn
-- License: BSD-3-Clause
-- Maintainer: exal59@yahoo.com
--
-- Support for operations on polynomials and monomials, including checking
module SymHask.Symbolic.Polynomial
    ( algebraicExpand
    , coeffVarMonomial
    , coefficientGpe
    , coefficientSv
    , collectTerms
    , degreeGpe
    , degreeSv
    , denom
    , expandMainOp
    , isMonomialGpe
    , isMonomialSv
    , isPolynomialGpe
    , isPolynomialSv
    , isRationalGre
    , leadingCoefficientGpe
    , leadingCoefficientSv
    , numer
    , rationalExpand
    , rationalVariables
    , rationalise
    , variables
    ) where

import           Control.Monad                              (foldM)
import qualified Data.HashMap.Strict                        as HM
import qualified Data.HashSet                               as HS
import qualified Data.List.NonEmpty                         as NE
import           SymHask.Symbolic
import           SymHask.Symbolic.Polynomial.Expansion
import           SymHask.Symbolic.Polynomial.Generalised
import           SymHask.Symbolic.Polynomial.Rational
import           SymHask.Symbolic.Polynomial.SingleVariable
import           SymHask.Symbolic.Simplification            ((.*.), (.+.))

{- | Collect like terms in a general polynomial expression.
Returns the collected form of u, or Undefined (Left) if u is not a GPE in S.
In collected form, u is a GME in S or a sum of GMEs with distinct variable parts.
-}
collectTerms :: SimplifiedExpr -> HS.HashSet SimplifiedExpr -> EvalResult SimplifiedExpr
collectTerms u vars
  | not (isPolynomialGpe u vars) =
      Left $ UnsupportedOperation "collectTerms: expression is not a GPE"
  | u `HS.member` vars = pure u -- already a single variable, which is a GME
  | otherwise = case u of
      Sum' terms -> collectFromSum (NE.toList terms) vars
      _          -> pure u -- already a single monomial, in collected form

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
        Nothing       -> pure $ mkNumber 0
        Just termList -> simplify $ mkSum termList
