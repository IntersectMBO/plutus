\begin{code}
module Scoped.Extrication.Reduction where

open import Type
open import Type.BetaNormal
open import Algorithmic as A
open import Scoped
open import Scoped.Extrication
open import Scoped.Extrication.RenamingSubstitution
open import Algorithmic.Reduction as AR
open import Algorithmic.Evaluation as AE
open import Scoped.Reduction as SR


open import Relation.Binary.PropositionalEquality as Eq

open import Data.Sum
open import Utils

extricate—→ : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K}{t t' : Γ ⊢ A}
  → t AR.—→ t' → extricate t SR.—→ extricate t'
extricateVal : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K}{t : Γ ⊢ A}
  → AR.Value t → SR.Value (extricate t)
extricateE : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}{t : Γ ⊢ A}
  → AR.Error t → SR.Error (extricate t)
extricateE E-error = E-error _
extricateE (E-·₁ p) = E-·₁ (extricateE p)
extricateE (E-·₂ p) = E-·₂ (extricateE p)
extricateE (E-·⋆ p) = E-·⋆ (extricateE p)
extricateE (E-unwrap p) = E-unwrap (extricateE p)
extricateE (E-builtin bn σ tel Bs Ds vtel x p tel') = E-builtin (extricateE x)

extricateVal V-ƛ = V-ƛ "x" _ _
extricateVal V-Λ_ = SR.V-Λ "x" _ _
extricateVal V-wrap1 = V-wrap _ _ _
extricateVal (V-con cn) = V-con (extricateC cn)

extricate—→ (ξ-·₁ p)   = ξ-·₁ (extricate—→ p)
extricate—→ (ξ-·₂ p q) = ξ-·₂ (extricateVal p) (extricate—→ q)
extricate—→ (ξ-·⋆ p) = ξ-·⋆ (extricate—→ p)
extricate—→ (β-ƛ {A = A}{N = N}{W = W} p) = Eq.subst
  (ƛ "x" (extricateNf⋆ A) (extricate N) · extricate W  SR.—→_)
  (lem[] N W)
  SR.β-ƛ
extricate—→ (β-Λ {K = K}{N = N}{W = W}) = Eq.subst
  (Λ "x" (extricateK K) (extricate N) ·⋆ extricateNf⋆ W SR.—→_)
  (lem[]⋆ N W)
  SR.β-Λ
extricate—→ β-wrap1 = β-wrap
extricate—→ (ξ-unwrap1 p) = ξ-unwrap (extricate—→ p)
extricate—→ (β-builtin bn σ tel vtel) = {!!}
extricate—→ (ξ-builtin bn σ tel Bs Ds vtel p p' tel') = {!SR.ξ-builtin {b = bn} ? (extricate—→ p) ?!}
\end{code}
