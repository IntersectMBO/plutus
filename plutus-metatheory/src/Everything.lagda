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

import Declarative
import Declarative.RenamingSubstitution
-- import Declarative.Erasure -- TODO

import Declarative.Examples
import Declarative.Examples.StdLib.Function
import Declarative.Examples.StdLib.ChurchNat
import Declarative.Examples.StdLib.Nat

-- Terms, reduction and evaluation where terms are indexed by normal
-- types

import Algorithmic
import Algorithmic.RenamingSubstitution
import Algorithmic.Reduction
import Algorithmic.Evaluation
import Algorithmic.Main
import Algorithmic.Soundness
import Algorithmic.Completeness
import Algorithmic.Erasure
import Algorithmic.Erasure.RenamingSubstitution
import Algorithmic.Erasure.Reduction
import Algorithmic.CK
import Algorithmic.CEKD
import Algorithmic.CEKC
import Algorithmic.CEKV

import Algorithmic.Examples

-- Untyped terms, reduction and evaluation

import Untyped
import Untyped.RenamingSubstitution
import Untyped.Reduction

-- Extrinsically typed terms, reduction and evaluation
import Scoped
import Scoped.RenamingSubstitution

import Scoped.Reduction

import Scoped.Extrication
import Scoped.Extrication.RenamingSubstitution
--import Scoped.Extrication.Reduction

import Scoped.Erasure
import Scoped.Erasure.RenamingSubstitution
--import Scoped.Erasure.Reduction

import Scoped.CK

import Check
import Main
\end{code}

