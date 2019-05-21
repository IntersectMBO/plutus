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
extricateE (E-builtin bn σ tel Bs Ds telB vtel e p telD) =
  E-builtin (extricateE e)

extricateVal V-ƛ = V-ƛ _ _ _
extricateVal V-Λ_ = SR.V-Λ _ _ _
extricateVal V-wrap1 = V-wrap _ _ _
extricateVal (V-con cn) = V-con (extricateC cn)

extricateVTel :  ∀ {Φ} Γ Δ (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
  (As : List (Δ ⊢Nf⋆ *))
  (tel : A.Tel Γ Δ σ As)
  → AR.VTel Γ Δ σ As tel
  → SR.VTel (len Γ) (extricateTel σ As tel)

extricateVTel Γ Δ σ []       _ _ = tt
extricateVTel Γ Δ σ (A ∷ As) (t Σ., tel) (v Σ., vtel) =
  extricateVal v ,, extricateVTel Γ Δ σ As tel vtel


extricate—→ (ξ-·₁ p)   = ξ-·₁ (extricate—→ p)
extricate—→ (ξ-·₂ p q) = ξ-·₂ (extricateVal p) (extricate—→ q)
extricate—→ (ξ-·⋆ p) = ξ-·⋆ (extricate—→ p)
extricate—→ (β-ƛ {A = A}{N = N}{W = W}) = Eq.subst
  (ƛ _ (extricateNf⋆ A) (extricate N) · extricate W  SR.—→_)
  (lem[] N W)
  SR.β-ƛ
extricate—→ (β-Λ {K = K}{N = N}{W = W}) = Eq.subst
  (Λ _ (extricateK K) (extricate N) ·⋆ extricateNf⋆ W SR.—→_)
  (lem[]⋆ N W)
  SR.β-Λ
extricate—→ β-wrap1 = β-wrap
extricate—→ (ξ-unwrap1 p) = ξ-unwrap (extricate—→ p)
extricate—→ (β-builtin addInteger σ _ vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) =
  β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG addInteger))) _ vtel)
extricate—→ (β-builtin subtractInteger σ _ vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) =
  β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG subtractInteger))) _ vtel)
extricate—→ (β-builtin multiplyInteger σ _ vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) =
  β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG multiplyInteger))) _ vtel)
extricate—→ (β-builtin divideInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) with ∣ j ∣ Data.Nat.≟ 0 | SR.β-builtin {b = divideInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG divideInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG divideInteger))) _ vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin quotientInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) with ∣ j ∣ Data.Nat.≟ 0 | SR.β-builtin {b = quotientInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG quotientInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG quotientInteger))) _ vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin remainderInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) with ∣ j ∣ Data.Nat.≟ 0 | SR.β-builtin {b = remainderInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG remainderInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG remainderInteger))) _ vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin modInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) with ∣ j ∣ Data.Nat.≟ 0 | SR.β-builtin {b = modInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG modInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG modInteger))) _ vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin lessThanInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) with i Builtin.Constant.Type.<? j | SR.β-builtin {b = lessThanInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG lessThanInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG lessThanInteger))) _ vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin lessThanEqualsInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) with i Data.Integer.≤? j | SR.β-builtin {b = lessThanEqualsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG lessThanEqualsInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG lessThanEqualsInteger))) _ vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin greaterThanInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) with i Builtin.Constant.Type.>? j | SR.β-builtin {b = greaterThanInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG greaterThanInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG greaterThanInteger))) _ vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin greaterThanEqualsInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) with i Builtin.Constant.Type.≥? j | SR.β-builtin {b = greaterThanEqualsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG greaterThanEqualsInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG greaterThanEqualsInteger))) _ vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin equalsInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) with i Data.Integer.≟ j | SR.β-builtin {b = equalsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG equalsInteger))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG equalsInteger))) _ vtel) 
... | yes p | r = r
... | no ¬p | r = r
extricate—→ (β-builtin concatenate σ tel vtel@(V-con (bytestring b) ,, V-con (bytestring b') ,, tt)) =
  SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG concatenate))) _ vtel) 
extricate—→ (β-builtin takeByteString σ tel vtel@(V-con (integer i) ,, V-con (bytestring b) ,, tt)) =
  SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG takeByteString))) _ vtel)
extricate—→ (β-builtin dropByteString σ tel vtel@(V-con (integer i) ,, V-con (bytestring b) ,, tt)) =
  SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG dropByteString))) _ vtel)
extricate—→ (β-builtin sha2-256 σ tel vtel@(V-con (bytestring b) ,, tt)) = SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG sha2-256))) _ vtel)
extricate—→ (β-builtin sha3-256 σ tel vtel@(V-con (bytestring b) ,, tt)) = SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG sha3-256))) _ vtel)
extricate—→ (β-builtin verifySignature σ tel vtel@(V-con (bytestring k) ,, V-con (bytestring d) ,, V-con (bytestring c) ,, tt)) with verifySig k d c | SR.β-builtin {b = verifySignature}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG verifySignature))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG verifySignature))) _ vtel) 
... | just true  | r = r
... | just false | r = r
... | nothing    | r = r
extricate—→ (β-builtin equalsByteString σ tel vtel@(V-con (bytestring b) ,, V-con (bytestring b') ,, tt)) with equals b b' | SR.β-builtin {b = equalsByteString}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG equalsByteString))) tel}  (extricateVTel _ _ σ (proj₁ (proj₂ (SIG equalsByteString))) _ vtel) 
... | true  | r = r
... | false | r = r
extricate—→ {Γ = Γ} (ξ-builtin addInteger σ tel [] .(con integer ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = addInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG addInteger))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con integer ∷ []) _)
extricate—→ (ξ-builtin addInteger σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = addInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG addInteger))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin addInteger σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin addInteger σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin subtractInteger σ tel [] .(con integer ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = subtractInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG subtractInteger))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con integer ∷ []) _)
extricate—→ (ξ-builtin subtractInteger σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = subtractInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG subtractInteger))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin subtractInteger σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin subtractInteger σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin multiplyInteger σ tel [] .(con integer ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = multiplyInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG multiplyInteger))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con integer ∷ []) _)
extricate—→ (ξ-builtin multiplyInteger σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = multiplyInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG multiplyInteger))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin multiplyInteger σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin multiplyInteger σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin divideInteger σ tel [] .(con integer ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = divideInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG divideInteger))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con integer ∷ []) _)
extricate—→ (ξ-builtin divideInteger σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = divideInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG divideInteger))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin divideInteger σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin divideInteger σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin quotientInteger σ tel [] .(con integer ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = quotientInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG quotientInteger))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con integer ∷ []) _)
extricate—→ (ξ-builtin quotientInteger σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = quotientInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG quotientInteger))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin quotientInteger σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin quotientInteger σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin remainderInteger σ tel [] .(con integer ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = remainderInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG remainderInteger))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con integer ∷ []) _)
extricate—→ (ξ-builtin remainderInteger σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = remainderInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG remainderInteger))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin remainderInteger σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin remainderInteger σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin modInteger σ tel [] .(con integer ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = modInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG modInteger))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con integer ∷ []) _)
extricate—→ (ξ-builtin modInteger σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = modInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG modInteger))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin modInteger σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin modInteger σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin lessThanInteger σ tel [] .(con integer ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = lessThanInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG lessThanInteger))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con integer ∷ []) _)
extricate—→ (ξ-builtin lessThanInteger σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = lessThanInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG lessThanInteger))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) _
extricate—→ (ξ-builtin lessThanInteger σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin lessThanInteger σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin lessThanEqualsInteger σ tel [] .(con integer ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = lessThanEqualsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG lessThanEqualsInteger))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con integer ∷ []) _)
extricate—→ (ξ-builtin lessThanEqualsInteger σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = lessThanEqualsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG lessThanEqualsInteger))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin lessThanEqualsInteger σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin lessThanEqualsInteger σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin greaterThanInteger σ tel [] .(con integer ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = greaterThanInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG greaterThanInteger))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con integer ∷ []) _)
extricate—→ (ξ-builtin greaterThanInteger σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = greaterThanInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG greaterThanInteger))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin greaterThanInteger σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin greaterThanInteger σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin greaterThanEqualsInteger σ tel [] .(con integer ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = greaterThanEqualsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG greaterThanEqualsInteger))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con integer ∷ []) _)
extricate—→ (ξ-builtin greaterThanEqualsInteger σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = greaterThanEqualsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG greaterThanEqualsInteger))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin greaterThanEqualsInteger σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin greaterThanEqualsInteger σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin equalsInteger σ tel [] .(con integer ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = equalsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG equalsInteger))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con integer ∷ []) _)
extricate—→ (ξ-builtin equalsInteger σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = equalsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG equalsInteger))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin equalsInteger σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin equalsInteger σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin concatenate σ tel [] .(con bytestring ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = concatenate}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG concatenate))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con bytestring ∷ []) _)
extricate—→ (ξ-builtin concatenate σ tel (.(con bytestring) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = concatenate}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG concatenate))) tel}(extricateVTel _ _ σ (con bytestring ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin concatenate σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin concatenate σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin takeByteString σ tel [] .(con bytestring ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = takeByteString}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG takeByteString))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con bytestring ∷ []) _)
extricate—→ (ξ-builtin takeByteString σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = takeByteString}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG takeByteString))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin takeByteString σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin takeByteString σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin dropByteString σ tel [] .(con bytestring ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = dropByteString}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG dropByteString))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con bytestring ∷ []) _)
extricate—→ (ξ-builtin dropByteString σ tel (.(con integer) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = dropByteString}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG dropByteString))) tel}(extricateVTel _ _ σ (con integer ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin dropByteString σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin dropByteString σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin sha2-256 σ tel [] .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = sha2-256}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG sha2-256))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin sha2-256 σ tel (B ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin sha2-256 σ tel (B ∷ B' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin sha3-256 σ tel [] .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = sha3-256}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG sha3-256))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin sha3-256 σ tel (B ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin sha3-256 σ tel (B ∷ B' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin verifySignature σ tel [] .(con bytestring ∷ con bytestring ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = verifySignature}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG verifySignature))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con bytestring ∷ con bytestring ∷ []) _)
extricate—→ (ξ-builtin verifySignature σ tel (.(con bytestring) ∷ []) .(con bytestring ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = verifySignature}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG verifySignature))) tel}(extricateVTel _ _ σ (con bytestring ∷ []) _ vtel) (extricate—→ p) (extricateTel σ (con bytestring ∷ []) _)
extricate—→ (ξ-builtin verifySignature σ tel (.(con bytestring) ∷ .(con bytestring) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = verifySignature}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG verifySignature))) tel}(extricateVTel _ _ σ (con bytestring ∷ con bytestring ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin verifySignature σ tel (B ∷ B' ∷ B'' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin verifySignature σ tel (B ∷ B' ∷ B'' ∷ B''' ∷ Bs) Ds telB telD vtel p ())

extricate—→ {Γ = Γ} (ξ-builtin equalsByteString σ tel [] .(con bytestring ∷ []) telB telD vtel p refl) =
  SR.ξ-builtin {b = equalsByteString}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG equalsByteString))) tel}(extricateVTel Γ _ σ [] _ tt) (extricate—→ p) (extricateTel σ (con bytestring ∷ []) _)
extricate—→ (ξ-builtin equalsByteString σ tel (.(con bytestring) ∷ []) .[] telB telD vtel p refl) =
  SR.ξ-builtin {b = equalsByteString}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG equalsByteString))) tel}(extricateVTel _ _ σ (con bytestring ∷ []) _ vtel) (extricate—→ p) (extricateTel σ [] tt)
extricate—→ (ξ-builtin equalsByteString σ tel (B ∷ B' ∷ []) Ds telB telD vtel p ())
extricate—→ (ξ-builtin equalsByteString σ tel (B ∷ B' ∷ B'' ∷ Bs) Ds telB telD vtel p ())

-- extrication for a sequence of steps

extricate—→⋆ : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K}{t t' : Γ ⊢ A}
  → t AR.—↠ t' → extricate t SR.—→⋆ extricate t'
extricate—→⋆ refl—↠ = refl
extricate—→⋆ (trans—↠ r p) = _—→⋆_.trans (extricate—→ r) (extricate—→⋆ p)

lem-step : ∀{t t' t'' : ScopedTm Z}(p : t SR.—→ t')(r : t' ≡ t'') → SR.Progress.step (Eq.subst (SR._—→_ t) r p) ≡ step p
lem-step p refl = refl

-- given the result of intrinsic progress this gives rise to extrinsic progress
extricateProgress : ∀{A}{t : ∅ ⊢ A} → AR.Progress t  → SR.Progress (extricate t)
extricateProgress (step p)  = step (extricate—→ p)
extricateProgress (done v)  = done (extricateVal v)
extricateProgress (error e) = error (extricateE e)

extricate-progress· : ∀{A B}{t : ∅ ⊢ A ⇒ B}(p : AR.Progress t) → (u : ∅ ⊢ A)
  → extricateProgress (AR.progress· p u) ≡ SR.progress· (extricateProgress p) (extricate u)
extricate-progress· (step p)   u = refl
extricate-progress· (done (V-ƛ {A = A}{x = x}{N = N})) u = lem-step β-ƛ (lem[] N u)
extricate-progress· (error e)  u = refl

extricate-progress·⋆ : ∀{K x B}{t : ∅ ⊢ Π x B}(p : AR.Progress t) → (A : ∅ ⊢Nf⋆ K)
  → extricateProgress (AR.progress·⋆ p A) ≡ SR.progress·⋆ (extricateProgress p) (extricateNf⋆ A)
extricate-progress·⋆ (step p)    A = refl
extricate-progress·⋆ (done (V-Λ_ {N = N})) A = lem-step β-Λ (lem[]⋆ N A)
extricate-progress·⋆ (error e)   A = refl

extricate-progress-unwrap : ∀{K}{pat}{arg : ∅ ⊢Nf⋆ K}{t : ∅ ⊢ ne ((μ1 · pat) · arg)}(p : AR.Progress t)
  → extricateProgress (AR.progress-unwrap p) ≡ SR.progress-unwrap (extricateProgress p)
extricate-progress-unwrap (step p)  = refl
extricate-progress-unwrap (done V-wrap1) = refl
extricate-progress-unwrap (error e) = refl

extricateProgressTel : ∀{Φ Ψ}{Γ : Ctx Φ}
  {σ : ∀{K} → Ψ ∋⋆ K → Φ ⊢Nf⋆ K}
  {As : List (Ψ ⊢Nf⋆ *)} →
  (tel : A.Tel Γ Ψ σ As)
  → AR.TelProgress tel
  → SR.TelProgress (extricateTel σ As tel)
extricateProgressTel tel (done vtel)                       =
  done (extricateTel _ _ tel) (extricateVTel _ _ _ _ tel vtel)
extricateProgressTel tel (step Bs Ds telB vtelB p q telD)  =
  step
    (extricateTel _ _ tel)
    (extricateTel _ _ telB)
    (extricateVTel _ _ _ _ telB vtelB)
    (extricate—→ p)
    (extricateTel _ _ telD)
extricateProgressTel tel (error Bs Ds telB vtelB e q telD) =
  error
    (extricateTel _ _ tel)
    (extricateTel _ _ telB)
    (extricateVTel _ _ _ _ telB vtelB)
    (extricateE e)
    (extricateTel _ _ telD)

extricate-progress-builtin : ∀ bn
  (σ : ∀{J} → proj₁ (SIG bn) ∋⋆ J → ∅ ⊢Nf⋆ J)
  (tel : A.Tel ∅ (proj₁ (SIG bn)) σ (proj₁ (proj₂ (SIG bn))))
  (telp : AR.TelProgress tel)
  → extricateProgress (AR.progress-builtin bn σ tel telp)
    ≡
    SR.progress-builtin
      bn
      (extricateSub σ)
      (extricateTel σ (proj₁ (proj₂ (SIG bn))) tel)
      (extricateProgressTel tel telp)
extricate-progress-builtin bn σ tel telp = ?

extricate-progress : ∀{A}(t : ∅ ⊢ A) → extricateProgress (AR.progress t) ≡ SR.progress (extricate t)
extricate-progress (ƛ x t) = refl
extricate-progress (t · u) = Eq.trans
  (extricate-progress· (AR.progress t) u)
  (cong (λ p → SR.progress· p (extricate u)) (extricate-progress t))
extricate-progress (Λ x t) = refl
extricate-progress (t ·⋆ A) = Eq.trans
  (extricate-progress·⋆ (AR.progress t) A)
  (cong (λ p → SR.progress·⋆ p (extricateNf⋆ A)) (extricate-progress t))
extricate-progress (wrap1 pat arg t) = refl
extricate-progress (unwrap1 t) = Eq.trans
  (extricate-progress-unwrap (AR.progress t))
  (cong SR.progress-unwrap (extricate-progress t))
extricate-progress (con x) = refl
extricate-progress (builtin addInteger σ tel) = {!!}
extricate-progress (builtin subtractInteger σ tel) = {!!}
extricate-progress (builtin multiplyInteger σ tel) = {!!}
extricate-progress (builtin divideInteger σ tel) = {!!}
extricate-progress (builtin quotientInteger σ tel) = {!!}
extricate-progress (builtin remainderInteger σ tel) = {!!}
extricate-progress (builtin modInteger σ tel) = {!!}
extricate-progress (builtin lessThanInteger σ tel) = {!!}
extricate-progress (builtin lessThanEqualsInteger σ tel) = {!!}
extricate-progress (builtin greaterThanInteger σ tel) = {!!}
extricate-progress (builtin greaterThanEqualsInteger σ tel) = {!!}
extricate-progress (builtin equalsInteger σ tel) = {!!}
extricate-progress (builtin concatenate σ tel) = {!!}
extricate-progress (builtin takeByteString σ tel) = {!!}
extricate-progress (builtin dropByteString σ tel) = {!!}
extricate-progress (builtin sha2-256 σ tel) = {!!}
extricate-progress (builtin sha3-256 σ tel) = {!!}
extricate-progress (builtin verifySignature σ tel) = {!!}
extricate-progress (builtin equalsByteString σ tel) = {!!}
extricate-progress (error A) = refl
\end{code}
