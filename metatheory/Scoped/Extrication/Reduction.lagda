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
open import Function
open import Data.Sum
open import Utils
open import Data.Product renaming (_,_ to _,,_)
open import Data.List
open import Data.Unit
open import Data.Nat
open import Data.Integer
open import Relation.Nullary

open import Builtin
open import Builtin.Constant.Term
open import Builtin.Constant.Type


open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf 

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

extricateVTel :  ∀ {Φ} Γ Δ (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)(As : List (Δ ⊢Nf⋆ *)) → VTel Γ Δ σ As → List (Σ (ScopedTm (len Γ)) (SR.Value {len⋆ Φ}{len Γ}))  
extricateVTel Γ Δ σ [] vtel = []
extricateVTel Γ Δ σ (A ∷ As) (t Σ., v Σ., vtel) =
  (extricate t ,, extricateVal v) ∷ extricateVTel Γ Δ σ As vtel

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
extricate—→ (β-builtin addInteger σ _ vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) =
  β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG addInteger))) vtel)
extricate—→ (β-builtin subtractInteger σ _ vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) =
  β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG subtractInteger))) vtel)
extricate—→ (β-builtin multiplyInteger σ _ vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) =
  β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG multiplyInteger))) vtel)
extricate—→ (β-builtin divideInteger σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) with ∣ j ∣ Data.Nat.≟ 0 | SR.β-builtin {b = divideInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG divideInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG subtractInteger))) vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin quotientInteger σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) with ∣ j ∣ Data.Nat.≟ 0 | SR.β-builtin {b = quotientInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG quotientInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG subtractInteger))) vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin remainderInteger σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) with ∣ j ∣ Data.Nat.≟ 0 | SR.β-builtin {b = remainderInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG remainderInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG subtractInteger))) vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin modInteger σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) with ∣ j ∣ Data.Nat.≟ 0 | SR.β-builtin {b = modInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG modInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG subtractInteger))) vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin lessThanInteger σ tel vtel) = {!!}
extricate—→ (β-builtin lessThanEqualsInteger σ tel vtel) = {!!}
extricate—→ (β-builtin greaterThanInteger σ tel vtel) = {!!}
extricate—→ (β-builtin greaterThanEqualsInteger σ tel vtel) = {!!}
extricate—→ (β-builtin equalsInteger σ tel vtel) = {!!}
extricate—→ (β-builtin concatenate σ tel vtel) = {!!}
extricate—→ (β-builtin takeByteString σ tel vtel) = {!!}
extricate—→ (β-builtin dropByteString σ tel vtel) = {!!}
extricate—→ (β-builtin sha2-256 σ tel vtel) = {!!}
extricate—→ (β-builtin sha3-256 σ tel vtel) = {!!}
extricate—→ (β-builtin verifySignature σ tel vtel) = {!!}
extricate—→ (β-builtin equalsByteString σ tel vtel) = {!!} -- Eq.subst (builtin bn (extricateSub σ) (extricateTel σ (proj₁ (proj₂ (SIG bn))) tel) SR.—→_) {!!} (β-builtin (extricateVTel _ _ σ _ vtel))
extricate—→ (ξ-builtin bn σ tel Bs Ds vtel p p' tel') = {!SR.ξ-builtin {b = bn} ? ? ?!}
\end{code}
