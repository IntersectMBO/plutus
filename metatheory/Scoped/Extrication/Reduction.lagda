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
open import Data.Bool
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

extricateVal V-ƛ = V-ƛ _ _ _
extricateVal V-Λ_ = SR.V-Λ _ _ _
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
  (ƛ _ (extricateNf⋆ A) (extricate N) · extricate W  SR.—→_)
  (lem[] N W)
  SR.β-ƛ
extricate—→ (β-Λ {K = K}{N = N}{W = W}) = Eq.subst
  (Λ _ (extricateK K) (extricate N) ·⋆ extricateNf⋆ W SR.—→_)
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
extricate—→ (β-builtin divideInteger σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) with ∣ j ∣ Data.Nat.≟ 0 | SR.β-builtin {b = divideInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG divideInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG divideInteger))) vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin quotientInteger σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) with ∣ j ∣ Data.Nat.≟ 0 | SR.β-builtin {b = quotientInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG quotientInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG quotientInteger))) vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin remainderInteger σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) with ∣ j ∣ Data.Nat.≟ 0 | SR.β-builtin {b = remainderInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG remainderInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG remainderInteger))) vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin modInteger σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) with ∣ j ∣ Data.Nat.≟ 0 | SR.β-builtin {b = modInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG modInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG modInteger))) vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin lessThanInteger σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) with i Builtin.Constant.Type.<? j | SR.β-builtin {b = lessThanInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG lessThanInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG lessThanInteger))) vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin lessThanEqualsInteger σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) with i Data.Integer.≤? j | SR.β-builtin {b = lessThanEqualsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG lessThanEqualsInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG lessThanEqualsInteger))) vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin greaterThanInteger σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) with i Builtin.Constant.Type.>? j | SR.β-builtin {b = greaterThanInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG greaterThanInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG greaterThanInteger))) vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin greaterThanEqualsInteger σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) with i Builtin.Constant.Type.≥? j | SR.β-builtin {b = greaterThanEqualsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG greaterThanEqualsInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG greaterThanEqualsInteger))) vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin equalsInteger σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (integer j) ,, tt)) with i Data.Integer.≟ j | SR.β-builtin {b = equalsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG equalsInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG equalsInteger))) vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin concatenate σ tel vtel@(_ ,, V-con (bytestring b) ,, _ ,, V-con (bytestring b') ,, tt)) =
  SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG concatenate))) vtel) 
extricate—→ (β-builtin takeByteString σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (bytestring b) ,, tt)) =
  SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG takeByteString))) vtel)
extricate—→ (β-builtin dropByteString σ tel vtel@(_ ,, V-con (integer i) ,, _ ,, V-con (bytestring b) ,, tt)) =
  SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG dropByteString))) vtel)
extricate—→ (β-builtin sha2-256 σ tel vtel@(_ ,, V-con (bytestring b) ,, tt)) = SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG sha2-256))) vtel)
extricate—→ (β-builtin sha3-256 σ tel vtel@(_ ,, V-con (bytestring b) ,, tt)) = SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG sha3-256))) vtel)
extricate—→ (β-builtin verifySignature σ tel vtel@(_ ,, V-con (bytestring k) ,, _ ,, V-con (bytestring d) ,, _ ,, V-con (bytestring c) ,, tt)) with verifySig k d c | SR.β-builtin {b = verifySignature}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG verifySignature))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG verifySignature))) vtel) 
... | just true  | r = r
... | just false | r = r
... | nothing    | r = r
extricate—→ (β-builtin equalsByteString σ tel vtel@(_ ,, V-con (bytestring b) ,, _ ,, V-con (bytestring b') ,, tt)) with equals b b' | SR.β-builtin {b = equalsByteString}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG equalsByteString))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG equalsByteString))) vtel) 
... | true  | r = r
... | false | r = r
extricate—→ (ξ-builtin bn σ tel Bs Ds vtel p p' tel') = {!SR.ξ-builtin {b = bn} ? ? ?!}
\end{code}
