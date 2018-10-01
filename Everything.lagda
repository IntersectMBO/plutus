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

-- EXPERIMENTS

-- an experiment with a BSN style normaliser
import Type.BSN
-- an experiment with a beta-eta NBE algorithm
import Type.BetaEtaNormal
import Type.BetaEtaNBE
-- a beta-eta nbe proof with the uniformity condition embedded in
-- values, the proof uses extensionality. The proof approach for
-- betaNBE below is cleaner and doesn't use extensionality and could
-- be reused here
import Type.BetaEtaNBEWithProofs

-- a partial attempt to index terms by weak head normal types
import ValueTypes.Term
import ValueTypes.Term.RenamingSubstitution
import ValueTypes.Term.Reduction
import ValueTypes.Evaluation
import ValueTypes.Examples

-- a partial attempt to index terms by syntactic types
-- where conversion takes a reflexive transitive closure
-- of reduction as an argument
import ConversionRTCReduction.Term
import ConversionRTCReduction.Term.RenamingSubstitution
import ConversionRTCReduction.Term.Reduction
import ConversionRTCReduction.Evaluation
import ConversionRTCReduction.Examples

-- a partial attempt to index terms by syntactic types
-- where conversion takes a single step of reduction
-- as an argument
import ConversionReduction.Term
import ConversionReduction.Term.RenamingSubstitution
import ConversionReduction.Term.Reduction
import ConversionReduction.Evaluation
import ConversionReduction.Examples
\end{code}
