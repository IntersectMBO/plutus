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

open import Relation.Nullary


open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con

extricate—→ : {A : ∅ ⊢Nf⋆ *}{t t' : ∅ ⊢ A}
  → t AR.—→ t' → extricate t SR.—→ extricate t'

extricateVal : {A : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A}
  → AR.Value t → SR.Value (extricate t)
extricateE : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}{t : Γ ⊢ A}
  → AR.Error t → SR.Error (extricate t)
extricateE E-error = E-error _

extricateVal (V-ƛ _) = V-ƛ _ _
extricateVal (V-Λ _) = V-Λ _
extricateVal (V-wrap p) = V-wrap _ _ (extricateVal p)
extricateVal (V-con cn) = V-con (extricateC cn)

extricate-decIf : ∀{X Φ}{Γ : A.Ctx Φ}{A : Φ ⊢Nf⋆ *}(p : Dec X)(t f : Γ A.⊢ A) → decIf p (extricate t) (extricate f) ≡ extricate (decIf p t f)
extricate-decIf (yes p) t f = refl
extricate-decIf (no ¬p) t f = refl


extricate-if : ∀{Φ}{Γ : A.Ctx Φ}{A : Φ ⊢Nf⋆ *}(b : Bool)(t f : Γ A.⊢ A) → (if b then extricate t else extricate f) ≡ extricate (if b then t else f)
extricate-if Bool.true  t f = refl
extricate-if Bool.false t f = refl


extricate-VERIFYSIG : ∀{Φ}{Γ : Ctx Φ}(p : Maybe Bool) → SR.VERIFYSIG p ≡ extricate {Φ}{Γ} (AR.VERIFYSIG p)
extricate-VERIFYSIG (just Bool.false) = refl
extricate-VERIFYSIG (just Bool.true)  = refl
extricate-VERIFYSIG nothing           = refl


extricate—→ (ξ-·₁ p)   = ξ-·₁ (extricate—→ p)
extricate—→ (ξ-·₂ p q) = ξ-·₂ (extricateVal p) (extricate—→ q)
extricate—→ (ξ-·⋆ p)   = ξ-·⋆ (extricate—→ p)

extricate—→ (ξ-wrap p) = ξ-wrap (extricate—→ p)
extricate—→ (β-ƛ {N = N}{V = V} p) = subst
  (ƛ _ (extricate N) · extricate V SR.—→_)
  (lem[] N V)
  (SR.β-ƛ (extricateVal p))
extricate—→ (β-Λ {N = N}{A = A}) = subst
  (Λ _ (extricate N) ·⋆ extricateNf⋆ A SR.—→_)
  (lem[]⋆ N A)
  SR.β-Λ
extricate—→ (β-wrap p) = β-wrap (extricateVal p)
extricate—→ (ξ-unwrap p) = ξ-unwrap (extricate—→ p)
{-
extricate—→ (β-builtin addInteger σ _ vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) =
  β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG addInteger))) _ vtel)
extricate—→ (β-builtin subtractInteger σ _ vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) =
  β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG subtractInteger))) _ vtel)
extricate—→ (β-builtin multiplyInteger σ _ vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) =
  β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG multiplyInteger))) _ vtel)
extricate—→ (β-builtin divideInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) =  Eq.subst
  (builtin divideInteger [] (con (integer i) ∷ con (integer j) ∷ []) SR.—→_)
  (extricate-decIf (∣ j ∣ Data.Nat.≟ 0) (error (con integer)) (con (integer (div i j))))
  (SR.β-builtin {b = divideInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG divideInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG divideInteger))) _ vtel))  
extricate—→ (β-builtin quotientInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = Eq.subst
  (builtin quotientInteger [] (con (integer i) ∷ con (integer j) ∷ []) SR.—→_)
  (extricate-decIf (∣ j ∣ Data.Nat.≟ 0) (error (con integer)) (con (integer (quot i j))))
  (SR.β-builtin {b = quotientInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG quotientInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG quotientInteger))) _ vtel)) 
extricate—→ (β-builtin remainderInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = Eq.subst
  (builtin remainderInteger [] (con (integer i) ∷ con (integer j) ∷ []) SR.—→_)
  (extricate-decIf (∣ j ∣ Data.Nat.≟ 0) (error (con integer)) (con (integer (rem i j))))
  (SR.β-builtin {b = remainderInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG remainderInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG remainderInteger))) _ vtel)) 
extricate—→ (β-builtin modInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = Eq.subst
  (builtin modInteger [] (con (integer i) ∷ con (integer j) ∷ []) SR.—→_)
  (extricate-decIf (∣ j ∣ Data.Nat.≟ 0) (error (con integer)) (con (integer (mod i j))))
  (SR.β-builtin {b = modInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG modInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG modInteger))) _ vtel))
extricate—→ (β-builtin lessThanInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = Eq.subst
  (builtin lessThanInteger [] (con (integer i) ∷ con (integer j) ∷ []) SR.—→_)
  (extricate-decIf (i Data.Integer.<? j) true false)
  (SR.β-builtin {b = lessThanInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG lessThanInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG lessThanInteger))) _ vtel))
extricate—→ (β-builtin lessThanEqualsInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = Eq.subst
  (builtin lessThanEqualsInteger [] (con (integer i) ∷ con (integer j) ∷ []) SR.—→_)
  (extricate-decIf (i Data.Integer.≤? j) true false)
  (SR.β-builtin {b = lessThanEqualsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG lessThanEqualsInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG lessThanEqualsInteger))) _ vtel))
extricate—→ (β-builtin greaterThanInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = Eq.subst
  (builtin greaterThanInteger [] (con (integer i) ∷ con (integer j) ∷ []) SR.—→_)
  (extricate-decIf (i Builtin.Constant.Type.>? j) true false)
  (SR.β-builtin {b = greaterThanInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG greaterThanInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG greaterThanInteger))) _ vtel))
extricate—→ (β-builtin greaterThanEqualsInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = Eq.subst
  (builtin greaterThanEqualsInteger [] (con (integer i) ∷ con (integer j) ∷ []) SR.—→_)
  (extricate-decIf (i Builtin.Constant.Type.≥? j) true false)
  (SR.β-builtin {b = greaterThanEqualsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG greaterThanEqualsInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG greaterThanEqualsInteger))) _ vtel))
extricate—→ (β-builtin equalsInteger σ tel vtel@(V-con (integer i) ,, V-con (integer j) ,, tt))  = Eq.subst
  (builtin equalsInteger [] (con (integer i) ∷ con (integer j) ∷ []) SR.—→_)
  (extricate-decIf (i Data.Integer.≟ j) true false)
  (SR.β-builtin {b = equalsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG equalsInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG equalsInteger))) _ vtel))
extricate—→ (β-builtin concatenate σ tel vtel@(V-con (bytestring b) ,, V-con (bytestring b') ,, tt)) =
  SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG concatenate))) _ vtel) 
extricate—→ (β-builtin takeByteString σ tel vtel@(V-con (integer i) ,, V-con (bytestring b) ,, tt)) =
  SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG takeByteString))) _ vtel)
extricate—→ (β-builtin dropByteString σ tel vtel@(V-con (integer i) ,, V-con (bytestring b) ,, tt)) =
  SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG dropByteString))) _ vtel)
extricate—→ (β-builtin sha2-256 σ tel vtel@(V-con (bytestring b) ,, tt)) = SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG sha2-256))) _ vtel)
extricate—→ (β-builtin sha3-256 σ tel vtel@(V-con (bytestring b) ,, tt)) = SR.β-builtin (extricateVTel _ _ σ (proj₁ (proj₂ (SIG sha3-256))) _ vtel)
extricate—→ (β-builtin verifySignature σ tel vtel@(V-con (bytestring k) ,, V-con (bytestring d) ,, V-con (bytestring c) ,, tt)) =  Eq.subst
  (builtin verifySignature [] (con (bytestring k) ∷ con (bytestring d) ∷ con (bytestring c) ∷ []) SR.—→_)
  (extricate-VERIFYSIG (verifySig k d c))
  (SR.β-builtin {b = verifySignature}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG verifySignature))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG verifySignature))) _ vtel))
extricate—→ (β-builtin equalsByteString σ tel vtel@(V-con (bytestring b) ,, V-con (bytestring b') ,, tt)) = Eq.subst
  (builtin equalsByteString [] (con (bytestring b) ∷ con (bytestring b') ∷ []) SR.—→_)
  (extricate-if (equals b b') true false)
  (SR.β-builtin {b = equalsByteString}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG equalsByteString))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG equalsByteString))) _ vtel))
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
-}

-- extrication for a sequence of steps

extricate—→⋆ : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}{t t' : Γ ⊢ A}
  → t AR.—↠ t' → extricate t SR.—→⋆ extricate t'
extricate—→⋆ refl—↠ = refl
extricate—→⋆ (trans—↠ r p) = _—→⋆_.trans (extricate—→ r) (extricate—→⋆ p)

lem-step : ∀{t t' t'' : ScopedTm Z}(p : t SR.—→ t')(r : t' ≡ t'')
  → SR.Progress.step (Eq.subst (SR._—→_ t) r p) ≡ step p
lem-step p refl = refl

-- given the result of intrinsic progress this gives rise to extrinsic progress
extricateProgress : ∀{A}{t : ∅ ⊢ A} → AR.Progress t
  → SR.Progress (extricate t)
extricateProgress (step p)    = step (extricate—→ p)
extricateProgress (done v)    = done (extricateVal v)
extricateProgress (error e)   = error (extricateE e)

-- proofs below

extricate-progress-· : ∀{A B}{t : ∅ ⊢ A ⇒ B}(p : AR.Progress t) → (u : ∅ ⊢ A)
  → extricateProgress (AR.progress-· p u) ≡ SR.progress· (extricateProgress p) (extricate u)
extricate-progress-· (step p)   u = refl
extricate-progress-· (done (V-ƛ {A = A}{x = x}{N = N})) u = lem-step β-ƛ (lem[] N u)
extricate-progress-· (error e)  u = refl

extricate-progress-·⋆ : ∀{K x B}{t : ∅ ⊢ Π x B}(p : AR.Progress t) → (A : ∅ ⊢Nf⋆ K)
  → extricateProgress (AR.progress-·⋆ p A) ≡ SR.progress·⋆ (extricateProgress p) (extricateNf⋆ A)
extricate-progress-·⋆ (step p)    A = refl
extricate-progress-·⋆ (done (V-Λ {N = N} p)) A = {!!} -- lem-step β-Λ (lem[]⋆ N A)
extricate-progress-·⋆ (error e)   A = refl

extricate-progress-unwrap : ∀{K}{pat}{arg : ∅ ⊢Nf⋆ K}{t : ∅ ⊢ ne ((μ · pat) · arg)}(p : AR.Progress t)
  → extricateProgress (AR.progress-unwrap p) ≡ SR.progress-unwrap (extricateProgress p)
extricate-progress-unwrap (step p)       = refl
extricate-progress-unwrap (done V-wrap1) = {!!} -- refl
extricate-progress-unwrap (error e)      = refl


open import Type.BetaNBE.RenamingSubstitution

cong₄ : ∀{A C : Set}{B : A → Set}{D : C → Set}{E : A → C → Set}(f : ∀{a} → B a → ∀{c} → D c → E a c)
  → (a : A)
  → {b b' : B a} → b ≡ b'
  → (c : C)
  → {d d' : D c} → d ≡ d'
  → f {a} b {c} d ≡ f {a} b' {c} d'
cong₄ f a refl c refl = refl
  
extricate-progress : ∀{A}(t : ∅ ⊢ A) → extricateProgress (AR.progress t) ≡ SR.progress (extricate t)
extricate-progress (ƛ x t) = refl
extricate-progress (t · u) = Eq.trans
  (extricate-progress-· (AR.progress t) u)
  (cong (λ p → SR.progress· p (extricate u)) (extricate-progress t))
extricate-progress (Λ x t) = {!!} -- refl
extricate-progress (t ·⋆ A) = Eq.trans
  (extricate-progress-·⋆ (AR.progress t) A)
  (cong (λ p → SR.progress·⋆ p (extricateNf⋆ A)) (extricate-progress t))
extricate-progress (wrap pat arg t) = {!!} -- refl
extricate-progress (unwrap t) = Eq.trans
  (extricate-progress-unwrap (AR.progress t))
  (cong SR.progress-unwrap (extricate-progress t))
extricate-progress (con x) = refl
extricate-progress (error A) = refl

-- we could extricate Finished separately
extricateSteps : {A : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A} → AE.Steps t →
  SR.Steps (extricate t)
extricateSteps (steps p (done N VN)) =
  _ ,, extricate—→⋆ p ,, inj₁ (just (extricateVal VN))
extricateSteps (steps p out-of-gas) = _ ,, extricate—→⋆ p ,, (inj₁ nothing)
extricateSteps (steps p (error e)) = _ ,, extricate—→⋆ p ,, inj₂ (extricateE e)

extricate-run—→ : ∀{A}{t t' : ∅ ⊢ A}(p : t AR.—→ t')(q : AE.Steps t') →
  extricateSteps (eval—→ p q) ≡ run—→ (extricate—→ p) (extricateSteps q)
extricate-run—→ p (steps q (done N VN)) = refl
extricate-run—→ p (steps q out-of-gas)  = refl
extricate-run—→ p (steps q (error e))   = refl

extricate-run : ∀{A}(t : ∅ ⊢ A) n
  → extricateSteps (eval (gas n) t) ≡ SR.run (extricate t) n

extricate-runProg : ∀{A}{t : ∅ ⊢ A}(p : AR.Progress t) n
  → extricateSteps (evalProg (gas n) p) ≡ SR.runProg n (extricateProgress p)

extricate-runProg (step p)  n = Eq.trans
  (extricate-run—→ p (eval (gas n) _))
  (cong (run—→ (extricate—→ p)) (extricate-run _ n))
extricate-runProg (done v)  n = refl
extricate-runProg (error e) n = refl

extricate-run t zero = refl
extricate-run t (ℕ.suc n) = Eq.trans
  (extricate-runProg (AR.progress t) n)
  (cong (runProg n) (extricate-progress t)) 
\end{code}
