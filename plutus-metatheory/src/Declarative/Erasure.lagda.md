---
title: Erasure of (Declarative) terms
layout: page
---

```
{-# OPTIONS --rewriting #-}

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
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con
  renaming (TermCon to TyTermCon)

open import Data.Empty
open import Data.Nat.Properties
open import Data.Nat
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec using ([]; _∷_;_++_)
open import Data.List using (List;length;[];_∷_)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (proj₁;proj₂)

len : ∀{Φ} → Ctx Φ → Set
len ∅        = ⊥
len (Γ ,⋆ K) = len Γ
len (Γ , A)  = Maybe (len Γ)

lenI : ∀{Φ} → Ctx Φ → Set
lenI ∅        = ⊥
lenI (Γ ,⋆ K) = Maybe (lenI Γ)
lenI (Γ , A)  = Maybe (lenI Γ)

len⋆ : Ctx⋆ → Set
len⋆ ∅        = ⊥
len⋆ (Γ ,⋆ K) = Maybe (len⋆ Γ)

eraseVar : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ ∋ A → len Γ
eraseVar Z     = nothing
eraseVar (S α) = just (eraseVar α)
eraseVar (T α) = eraseVar α

eraseTC : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢⋆ *} → TyTermCon A → TermCon
eraseTC (integer i)    = integer i
eraseTC (bytestring b) = bytestring b
eraseTC (string s)     = string s
eraseTC (bool b)       = bool b 
eraseTC unit           = unit
eraseTC (Data d)       = Data d

open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum
open import Data.Nat.Properties

erase : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ ⊢ A → len Γ ⊢

erase-Sub : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(σ⋆ : T.Sub Φ Ψ)
  → D.Sub Γ Δ σ⋆ → U.Sub (len Γ) (len Δ) 

erase (` α)           = ` (eraseVar α)
erase (ƛ t)           = ƛ (erase t) 
erase (t · u)         = erase t · erase u
erase (Λ t)           = delay (erase t)
erase (t ·⋆ A)        = force (erase t)
erase (wrap A B t)    = erase t
erase (unwrap t)      = erase t
erase (conv p t)      = erase t
erase {Γ = Γ} (con t) = con (eraseTC {Γ = Γ} t)
erase (builtin b)     = builtin b
erase (error A)       = error

backVar⋆ : ∀{Φ}(Γ : Ctx Φ) → len Γ → Φ ⊢⋆ *
backVar⋆ (Γ ,⋆ J) x       = T.weaken (backVar⋆ Γ x)
backVar⋆ (Γ , A) nothing  = A
backVar⋆ (Γ , A) (just x) = backVar⋆ Γ x

backVar : ∀{Φ}(Γ : Ctx Φ)(x : len Γ) → Γ ∋ (backVar⋆ Γ x)
backVar (Γ ,⋆ J) x        = T (backVar Γ x)
backVar (Γ , A)  nothing  = Z
backVar (Γ , A)  (just x) = S (backVar Γ x)

erase-Sub σ⋆ σ i = erase (σ (backVar _ i))
```
