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

extricate—→ : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}{t t' : Γ ⊢ A}
  → t AR.—→ t' → extricate t SR.—→ extricate t'

extricateVal : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}{t : Γ ⊢ A}
  → AR.Value t → SR.Value (extricate t)
extricateE : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}{t : Γ ⊢ A}
  → AR.Error t → SR.Error (extricate t)
extricateE E-error = E-error _

extricateVal V-ƛ = V-ƛ _ _
extricateVal V-Λ = V-Λ _
extricateVal (V-wrap p) = V-wrap _ _ (extricateVal p)
extricateVal (V-con cn) = V-con (extricateC cn)

extricateVTel :  ∀ {Φ} Γ Δ (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
  (As : List (Δ ⊢Nf⋆ *))
  (tel : A.Tel Γ Δ σ As)
  → AR.VTel Γ Δ σ As tel
  → SR.VTel (Data.List.length As) (len Γ) (extricateTel σ As tel)

extricateVTel Γ Δ σ []       _ _ = tt
extricateVTel Γ Δ σ (A ∷ As) (t ∷ tel) (v Σ., vtel) =
  extricateVal v ,, extricateVTel Γ Δ σ As tel vtel

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
extricate—→ (β-wrap1 p) = β-wrap (extricateVal p)
extricate—→ (ξ-unwrap1 p) = ξ-unwrap (extricate—→ p)
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



extricateProgressTel : ∀{Φ Ψ}{Γ : Ctx Φ}
  {σ : ∀{K} → Ψ ∋⋆ K → Φ ⊢Nf⋆ K}
  {As : List (Ψ ⊢Nf⋆ *)} →
  (tel : A.Tel Γ Ψ σ As)
  → AR.TelProgress tel
  → SR.TelProgress (extricateTel σ As tel)
{-
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

extricate-progress-unwrap : ∀{K}{pat}{arg : ∅ ⊢Nf⋆ K}{t : ∅ ⊢ ne ((μ1 · pat) · arg)}(p : AR.Progress t)
  → extricateProgress (AR.progress-unwrap p) ≡ SR.progress-unwrap (extricateProgress p)
extricate-progress-unwrap (step p)       = refl
extricate-progress-unwrap (done V-wrap1) = {!!} -- refl
extricate-progress-unwrap (error e)      = refl

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
extricate-progress-builtin addInteger σ _ (done (V-con (integer i) ,, V-con (integer j) ,, tt)) = refl
extricate-progress-builtin subtractInteger σ tel (done (V-con (integer i) ,, V-con (integer j) ,, tt)) = refl
extricate-progress-builtin multiplyInteger σ tel (done (V-con (integer i) ,, V-con (integer j) ,, tt)) = refl
extricate-progress-builtin divideInteger σ tel (done vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = lem-step
  (SR.β-builtin {b = divideInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG divideInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG divideInteger))) _ vtel))  
  (extricate-decIf (∣ j ∣ Data.Nat.≟ 0) (error (con integer)) (con (integer (div i j))))
extricate-progress-builtin quotientInteger σ tel (done vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = lem-step
  (SR.β-builtin {b = quotientInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG quotientInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG quotientInteger))) _ vtel))  
  (extricate-decIf (∣ j ∣ Data.Nat.≟ 0) (error (con integer)) (con (integer (quot i j))))
extricate-progress-builtin remainderInteger σ tel (done vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = lem-step
  (SR.β-builtin {b = remainderInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG remainderInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG remainderInteger))) _ vtel))  
  (extricate-decIf (∣ j ∣ Data.Nat.≟ 0) (error (con integer)) (con (integer (rem i j))))
extricate-progress-builtin modInteger σ tel (done vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = lem-step
  (SR.β-builtin {b = modInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG modInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG modInteger))) _ vtel))  
  (extricate-decIf (∣ j ∣ Data.Nat.≟ 0) (error (con integer)) (con (integer (mod i j))))
extricate-progress-builtin lessThanInteger σ tel (done vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = lem-step
  (SR.β-builtin {b = lessThanInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG lessThanInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG lessThanInteger))) _ vtel))  
  (extricate-decIf (i Data.Integer.<? j) true false)
extricate-progress-builtin lessThanEqualsInteger σ tel (done vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = lem-step
  (SR.β-builtin {b = lessThanEqualsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG lessThanEqualsInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG lessThanEqualsInteger))) _ vtel))  
  (extricate-decIf (i Data.Integer.≤? j) true false)
extricate-progress-builtin greaterThanInteger σ tel (done vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = lem-step
  (SR.β-builtin {b = greaterThanInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG greaterThanInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG greaterThanInteger))) _ vtel))  
  (extricate-decIf (i Builtin.Constant.Type.>? j) true false)
extricate-progress-builtin greaterThanEqualsInteger σ tel (done vtel@ (V-con (integer i) ,, V-con (integer j) ,, tt)) = lem-step
  (SR.β-builtin {b = greaterThanEqualsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG greaterThanEqualsInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG greaterThanEqualsInteger))) _ vtel))  
  (extricate-decIf (i Builtin.Constant.Type.≥? j) true false)
extricate-progress-builtin equalsInteger σ tel (done vtel@(V-con (integer i) ,, V-con (integer j) ,, tt)) = lem-step
  (SR.β-builtin {b = equalsInteger}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG equalsInteger))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG equalsInteger))) _ vtel))  
  (extricate-decIf (i Data.Integer.≟ j) true false)
extricate-progress-builtin concatenate σ tel (done (V-con (bytestring b) ,, V-con (bytestring b') ,, tt)) = refl
extricate-progress-builtin takeByteString σ tel (done (V-con (integer i) ,, V-con (bytestring b) ,, tt)) = refl
extricate-progress-builtin dropByteString σ tel (done (V-con (integer i) ,, V-con (bytestring b) ,, tt)) = refl
extricate-progress-builtin sha2-256 σ tel (done (V-con (bytestring b) ,, tt)) = refl
extricate-progress-builtin sha3-256 σ tel (done (V-con (bytestring b) ,, tt)) = refl
extricate-progress-builtin verifySignature σ tel (done vtel@(V-con (bytestring k) ,, V-con (bytestring d) ,, V-con (bytestring c) ,, tt)) = lem-step
  (SR.β-builtin {b = verifySignature}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG verifySignature))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG verifySignature))) _ vtel))  
  (extricate-VERIFYSIG (verifySig k d c))
extricate-progress-builtin equalsByteString σ tel (done vtel@(V-con (bytestring b) ,, V-con (bytestring b') ,, tt)) = lem-step
  (SR.β-builtin {b = equalsByteString}{As = []}{extricateTel σ (proj₁ (proj₂ (SIG equalsByteString))) tel} (extricateVTel _ _ σ (proj₁ (proj₂ (SIG equalsByteString))) _ vtel))  
  (extricate-if (equals b b') true false)
extricate-progress-builtin addInteger σ tel (step [] .(con integer ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin addInteger σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin addInteger σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin addInteger σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin subtractInteger σ tel (step [] .(con integer ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin subtractInteger σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin subtractInteger σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin subtractInteger σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin multiplyInteger σ tel (step [] .(con integer ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin multiplyInteger σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin multiplyInteger σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin multiplyInteger σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin divideInteger σ tel (step [] .(con integer ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin divideInteger σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin divideInteger σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin divideInteger σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin quotientInteger σ tel (step [] .(con integer ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin quotientInteger σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin quotientInteger σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin quotientInteger σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin remainderInteger σ tel (step [] .(con integer ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin remainderInteger σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin remainderInteger σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin remainderInteger σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin modInteger σ tel (step [] .(con integer ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin modInteger σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin modInteger σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin modInteger σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin lessThanInteger σ tel (step [] .(con integer ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin lessThanInteger σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin lessThanInteger σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin lessThanInteger σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin lessThanEqualsInteger σ tel (step [] .(con integer ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin lessThanEqualsInteger σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin lessThanEqualsInteger σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin lessThanEqualsInteger σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin greaterThanInteger σ tel (step [] .(con integer ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin greaterThanInteger σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin greaterThanInteger σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin greaterThanInteger σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin greaterThanEqualsInteger σ tel (step [] .(con integer ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin greaterThanEqualsInteger σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin greaterThanEqualsInteger σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin greaterThanEqualsInteger σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin equalsInteger σ tel (step [] .(con integer ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin equalsInteger σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin equalsInteger σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin equalsInteger σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin concatenate σ tel (step [] .(con bytestring ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin concatenate σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin concatenate σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin concatenate σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin takeByteString σ tel (step [] .(con bytestring ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin takeByteString σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin takeByteString σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin takeByteString σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin dropByteString σ tel (step [] .(con bytestring ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin dropByteString σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin dropByteString σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin dropByteString σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)

extricate-progress-builtin sha2-256 σ tel (step [] .[] telB vtelB p refl telD) = refl
extricate-progress-builtin sha2-256 σ tel (step (B ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin sha2-256 σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin sha3-256 σ tel (step [] .[] telB vtelB p refl telD) = refl
extricate-progress-builtin sha3-256 σ tel (step (B ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin sha3-256 σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin verifySignature σ tel (step [] .(con bytestring ∷ con bytestring ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin verifySignature σ tel (step (.(con bytestring) ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin verifySignature σ tel (step (.(con bytestring) ∷ .(con bytestring) ∷ []) .[] telB vtelB p refl telD) = refl
extricate-progress-builtin verifySignature σ tel (step (B ∷ B' ∷ B'' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin verifySignature σ tel (step (B ∷ B' ∷ B'' ∷ B''' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin equalsByteString σ tel (step [] .(con bytestring ∷ []) telB vtelB p refl telD) = refl
extricate-progress-builtin equalsByteString σ tel (step (._ ∷ []) Ds telB vtelB p refl telD) = refl
extricate-progress-builtin equalsByteString σ tel (step (B ∷ B' ∷ []) Ds telB vtelB p () telD)
extricate-progress-builtin equalsByteString σ tel (step (B ∷ B' ∷ B'' ∷ Bs) Ds telB vtelB p () telD)
extricate-progress-builtin addInteger σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin subtractInteger σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin multiplyInteger σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin divideInteger σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin quotientInteger σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin remainderInteger σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin modInteger σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin lessThanInteger σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin lessThanEqualsInteger σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin greaterThanInteger σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin greaterThanEqualsInteger σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin equalsInteger σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin concatenate σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin takeByteString σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin dropByteString σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin sha2-256 σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin sha3-256 σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin verifySignature σ tel (error Bs Ds telB vtelB e q telD) = refl
extricate-progress-builtin equalsByteString σ tel (error Bs Ds telB vtelB e q telD) = refl

open import Type.BetaNBE.RenamingSubstitution

extricateProgressTelCons-progressTelCons : ∀ Φ (A : Φ ⊢Nf⋆ *)(As : List (Φ ⊢Nf⋆ *)) → 
 (σ   : ∀{J} → Φ ∋⋆ J → ∅ ⊢Nf⋆ J)
 (t : ∅ ⊢ substNf σ A)
 (tp : AR.Progress t)
 (tel : A.Tel ∅ Φ σ As)
 (telp : AR.TelProgress tel)
 → extricateProgressTel {As = A ∷ As} (t ,, tel) (AR.progressTelCons tp telp)
   ≡
   SR.progressTelCons (extricateProgress tp) (extricateProgressTel tel telp)
extricateProgressTelCons-progressTelCons Φ A As σ t (step p)  tel telp = refl
extricateProgressTelCons-progressTelCons Φ A As σ t (error e) tel telp = refl
extricateProgressTelCons-progressTelCons Φ A As σ t (done vt) tel (done vtel) = refl
extricateProgressTelCons-progressTelCons Φ A As σ t (done vt) tel (step Bs Ds telB vtelB p q telD) = refl
extricateProgressTelCons-progressTelCons Φ A As σ t (done vt) tel (error Bs Ds telB vtelB e p telD) = refl



cong₄ : ∀{A C : Set}{B : A → Set}{D : C → Set}{E : A → C → Set}(f : ∀{a} → B a → ∀{c} → D c → E a c)
  → (a : A)
  → {b b' : B a} → b ≡ b'
  → (c : C)
  → {d d' : D c} → d ≡ d'
  → f {a} b {c} d ≡ f {a} b' {c} d'
cong₄ f a refl c refl = refl
  
extricate-progress : ∀{A}(t : ∅ ⊢ A) → extricateProgress (AR.progress t) ≡ SR.progress (extricate t)

extricateTel-progressTel : ∀ Φ (As : List (Φ ⊢Nf⋆ *)) → 
 (σ   : ∀{J} → Φ ∋⋆ J → ∅ ⊢Nf⋆ J)
 ( tel : A.Tel ∅ Φ σ As)
 → extricateProgressTel tel (AR.progressTel tel) ≡ SR.progressTel (extricateTel σ As tel)
extricateTel-progressTel Φ []       σ tt         = refl
extricateTel-progressTel Φ (A ∷ As) σ (t ,, tel) = Eq.trans
  (extricateProgressTelCons-progressTelCons Φ A As σ t (AR.progress t) tel (AR.progressTel tel))
  (cong₄
    {B = SR.Progress}
    SR.progressTelCons
    (extricate t)
    (extricate-progress t)
    (extricateTel _ _ tel)
    (extricateTel-progressTel Φ As σ tel))

extricate-progress (ƛ x t) = refl
extricate-progress (t · u) = Eq.trans
  (extricate-progress-· (AR.progress t) u)
  (cong (λ p → SR.progress· p (extricate u)) (extricate-progress t))
extricate-progress (Λ x t) = {!!} -- refl
extricate-progress (t ·⋆ A) = Eq.trans
  (extricate-progress-·⋆ (AR.progress t) A)
  (cong (λ p → SR.progress·⋆ p (extricateNf⋆ A)) (extricate-progress t))
extricate-progress (wrap1 pat arg t) = {!!} -- refl
extricate-progress (unwrap1 t) = Eq.trans
  (extricate-progress-unwrap (AR.progress t))
  (cong SR.progress-unwrap (extricate-progress t))
extricate-progress (con x) = refl
extricate-progress (builtin bn σ tel) = Eq.trans
  (extricate-progress-builtin bn σ tel (AR.progressTel tel))
  (cong (SR.progress-builtin bn (extricateSub σ) (extricateTel σ (proj₁ (proj₂ (SIG bn))) tel))
        (extricateTel-progressTel (proj₁ (SIG bn)) (proj₁ (proj₂ (SIG bn))) σ tel))
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
-}
\end{code}
