module SymHask.Symbolic.SemanticEquality
  ( semanticEq
  , semanticNeq
  , (=~=)  -- Infix operator for semantic equality
  , (=/=)  -- Infix operator for semantic inequality
  ) where

import SymHask.Symbolic (Expression)
import SymHask.Symbolic.Simplification.AutomaticSimplification (automaticSimplify)

-- | Semantic equality that uses simplification
semanticEq :: Expression -> Expression -> Bool
semanticEq u v = case (automaticSimplify u, automaticSimplify v) of
  (Right u', Right v') -> u' == v'  -- Uses structural equality
  _                    -> False

-- | Semantic inequality that uses simplification
semanticNeq :: Expression -> Expression -> Bool
semanticNeq u v = not (semanticEq u v)

-- | Infix operator for semantic equality
(=~=) :: Expression -> Expression -> Bool
(=~=) = semanticEq

-- | Infix operator for semantic inequality
(=/=) :: Expression -> Expression -> Bool
(=/=) = semanticNeq

infix 4 =~=, =/=
