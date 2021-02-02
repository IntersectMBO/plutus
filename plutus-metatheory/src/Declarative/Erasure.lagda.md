---
title: Erasure of (Declarative) terms
layout: page
---

```
module Declarative.Erasure where
```

```
open import Declarative
open import Declarative.RenamingSubstitution as D
open import Type.RenamingSubstitution as T
open import Untyped
open import Untyped.RenamingSubstitution as U
```

```
open import Type
open import Declarative
open import Builtin hiding (length)
open import Utils
open import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢⋆_ ` con
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con
  renaming (TermCon to TyTermCon)

open import Data.Nat.Properties
open import Data.Nat
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec using ([]; _∷_;_++_)
open import Data.List using (List;length;[];_∷_)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (proj₁;proj₂)

len : ∀{Φ} → Ctx Φ → ℕ
len ∅        = 0
len (Γ ,⋆ K) = len Γ
len (Γ , A)  = suc (len Γ)

lenI : ∀{Φ} → Ctx Φ → ℕ
lenI ∅        = 0
lenI (Γ ,⋆ K) = suc (lenI Γ)
lenI (Γ , A)  = suc (lenI Γ)

len⋆ : Ctx⋆ → ℕ
len⋆ ∅        = 0
len⋆ (Γ ,⋆ K) = suc (len⋆ Γ)

lemma : (b : Builtin)
  → len⋆ (proj₁ (SIG b)) + length (proj₁ (proj₂ (SIG b))) ≡ arity b
lemma addInteger = refl
lemma subtractInteger = refl
lemma multiplyInteger = refl
lemma divideInteger = refl
lemma quotientInteger = refl
lemma remainderInteger = refl
lemma modInteger = refl
lemma lessThanInteger = refl
lemma lessThanEqualsInteger = refl
lemma greaterThanInteger = refl
lemma greaterThanEqualsInteger = refl
lemma equalsInteger = refl
lemma concatenate = refl
lemma takeByteString = refl
lemma dropByteString = refl
lemma lessThanByteString = refl
lemma greaterThanByteString = refl
lemma sha2-256 = refl
lemma sha3-256 = refl
lemma verifySignature = refl
lemma equalsByteString = refl
lemma ifThenElse = refl
lemma charToString = refl
lemma append = refl
lemma trace = refl

lemma≤ : (b : Builtin) → len⋆ (proj₁ (SIG b)) + length (proj₁ (proj₂ (SIG b))) ≤‴ arity b
lemma≤ b rewrite lemma b = ≤‴-refl

eraseVar : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ ∋ A → Fin (len Γ)
eraseVar Z     = zero 
eraseVar (S α) = suc (eraseVar α) 
eraseVar (T α) = eraseVar α

eraseTC : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢⋆ *} → TyTermCon A → TermCon
eraseTC (integer i)    = integer i
eraseTC (bytestring b) = bytestring b
eraseTC (string s)     = string s
eraseTC (bool b)       = bool b 
eraseTC (char c)       = char c
eraseTC unit           = unit

open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum
open import Data.Nat.Properties

erase : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ ⊢ A → len Γ ⊢

erase-Sub : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(σ⋆ : T.Sub Φ Ψ)
  → D.Sub Γ Δ σ⋆ → U.Sub (len Γ) (len Δ) 

erase (` α)             = ` (eraseVar α)
erase (ƛ t)             = ƛ (erase t) 
erase (t · u)           = erase t · erase u
erase (Λ t)             = delay (erase t)
erase (t ·⋆ A)          = force (erase t)
erase (wrap A B t)      = erase t
erase (unwrap t)        = erase t
erase (conv p t)        = erase t
erase {Γ = Γ} (con t)   = con (eraseTC {Γ = Γ} t)
erase (ibuiltin b)      = builtin b
erase (error A)         = error

backVar⋆ : ∀{Φ}(Γ : Ctx Φ) → Fin (len Γ) → Φ ⊢⋆ *
backVar⋆ (Γ ,⋆ J) x = T.weaken (backVar⋆ Γ x)
backVar⋆ (Γ , A) zero = A
backVar⋆ (Γ , A) (suc x) = backVar⋆ Γ x

backVar : ∀{Φ}(Γ : Ctx Φ)(i : Fin (len Γ)) → Γ ∋ (backVar⋆ Γ i)
backVar (Γ ,⋆ J) i = T (backVar Γ i)
backVar (Γ , A) zero    = Z
backVar (Γ , A) (suc i) = S (backVar Γ i)

erase-Sub σ⋆ σ i = erase (σ (backVar _ i))
```
