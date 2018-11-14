\begin{code}
module Everything where

-- Types

import Type
import Type.RenamingSubstitution
import Type.Reduction
import Type.Equality

-- a beta NBE algorithm and accompanying soundness, completeness and
-- stability proofs and necessary equipment for substituting into
-- normal types by embedding back into syntax, substituting and
-- renormalising


import Type.BetaNormal
import Type.BetaNBE
import Type.BetaNBE.Soundness
import Type.BetaNBE.Completeness
import Type.BetaNBE.Stability
import Type.BetaNBE.RenamingSubstitution
-- a complete attempt to index terms by syntactic types where
-- conversion takes an equation as an argument. Evaluation only works
-- in the absense of conversions in terms.

-- Builtins
import Builtin.Signature
import Builtin.Constant.Type
import Builtin.Constant.Term

import TermIndexedBySyntacticType.Term
import TermIndexedBySyntacticType.Term.RenamingSubstitution
import TermIndexedBySyntacticType.Term.Reduction
import TermIndexedBySyntacticType.Evaluation

import TermIndexedBySyntacticType.Examples

-- Terms, reduction and evaluation where terms are indexed by normal
-- types

import TermIndexedByNormalType.Term
import TermIndexedByNormalType.Term.RenamingSubstitution
import TermIndexedByNormalType.Term.Reduction
import TermIndexedByNormalType.Evaluation
--import TermIndexedByNormalType.Examples
\end{code}
