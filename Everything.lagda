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

-- Terms, reduction and evaluation where terrms are
-- indexed by normal types
import NormalTypes.Term
import NormalTypes.Term.RenamingSubstitution
import NormalTypes.Term.Reduction
import NormalTypes.Evaluation
import NormalTypes.Examples

-- a complete attempt to index terms by syntactic types where
-- conversion takes an equation as an argument. Evaluation only works
-- in the absense of conversions in terms. This version of the syntax
-- is arguably the most standard
import ConversionEquality.Term
import ConversionEquality.Term.RenamingSubstitution
import ConversionEquality.Term.Reduction
import ConversionEquality.Evaluation
import ConversionEquality.Examples
\end{code}
