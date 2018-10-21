\begin{code}
module Everything where

-- Types
import Type
import Type.RenamingSubstitution
import Type.Reduction
import Type.Equality
import Type.BetaNormal

-- a beta NBE algorithm and accompanying soundness, completeness and
-- stability proofs and necessary equipment for substituting into
-- normal types by embedding back into syntax, substituting and
-- renormalising
import Type.BetaNBE
import Type.BetaNBE.Soundness
import Type.BetaNBE.Completeness
import Type.BetaNBE.Stability
import Type.BetaNBE.RenamingSubstitution

-- Terms, reduction and evaluation where terms are
-- indexed by normal types
import TermIndexedByNormalType.Term
import TermIndexedByNormalType.Term.RenamingSubstitution
import TermIndexedByNormalType.Term.Reduction
import TermIndexedByNormalType.Evaluation
--import TermIndexedByNormalType.Examples

-- a complete attempt to index terms by syntactic types where
-- conversion takes an equation as an argument. Evaluation only works
-- in the absense of conversions in terms. This version of the syntax
-- is arguably the most standard
import TermIndexedBySyntacticType.Term
import TermIndexedBySyntacticType.Term.RenamingSubstitution
import TermIndexedBySyntacticType.Term.Reduction
import TermIndexedBySyntacticType.Evaluation
--import TermIndexedBySyntacticType.Examples
\end{code}
