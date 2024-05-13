---
title: Scoped.RenamingSubstitution
layout: page
---
```
module Scoped.RenamingSubstitution where
```

```
open import Data.Nat using (ℕ;zero;suc)
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec using ([];_∷_)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;cong₂)

open import Utils using (List;[];_∷_)
open import Scoped using (ScopedTy;Tel;Tel⋆;Weirdℕ;WeirdFin;ScopedTm)
open ScopedTy
open ScopedTm
open Weirdℕ
open WeirdFin
open import Builtin.Constant.Type using (TyCon)
open TyCon
```

```
Ren⋆ : ℕ → ℕ → Set
Ren⋆ m n = Fin m → Fin n

lift⋆ : ∀{m n} → Ren⋆ m n → Ren⋆ (suc m) (suc n)
lift⋆ ρ zero    = zero
lift⋆ ρ (suc α) = suc (ρ α)

ren⋆ : ∀{m n} → Ren⋆ m n → ScopedTy m → ScopedTy n

ren⋆-List : ∀{m n} → Ren⋆ m n → List (ScopedTy m) → List (ScopedTy n)
ren⋆-List ρ [] = []
ren⋆-List ρ (x ∷ xs) = (ren⋆ ρ x) ∷ (ren⋆-List ρ xs)

ren⋆-ListList : ∀{m n} → Ren⋆ m n → List (List (ScopedTy m)) → List (List (ScopedTy n))
ren⋆-ListList ρ [] = []
ren⋆-ListList ρ (xs ∷ xss) = (ren⋆-List ρ xs) ∷ (ren⋆-ListList ρ xss)

ren⋆ ρ (` α)     = ` (ρ α)
ren⋆ ρ (A ⇒ B)   = ren⋆ ρ A ⇒ ren⋆ ρ B
ren⋆ ρ (Π K A)   = Π K (ren⋆ (lift⋆ ρ) A)
ren⋆ ρ (ƛ K A)   = ƛ K (ren⋆ (lift⋆ ρ) A)
ren⋆ ρ (A · B)   = ren⋆ ρ A · ren⋆ ρ B
ren⋆ ρ (con c)   = con c
ren⋆ ρ (μ A B)   = μ (ren⋆ ρ A) (ren⋆ ρ B)
ren⋆ ρ (SOP xss) = SOP (ren⋆-ListList ρ xss)

ren⋆T : ∀{m n o} → Ren⋆ m n → Tel⋆ m o → Tel⋆ n o
ren⋆T ρ⋆ []       = []
ren⋆T ρ⋆ (A ∷ As) = ren⋆ ρ⋆ A ∷ ren⋆T ρ⋆ As

Ren : ∀{m n} → Weirdℕ m → Weirdℕ n → Set
Ren m n = WeirdFin m → WeirdFin n

lift : ∀{m n}{w : Weirdℕ m}{v : Weirdℕ n} → Ren w v → Ren (S w) (S v)
lift ρ Z     = Z
lift ρ (S x) = S (ρ x)

⋆lift : ∀{m n}{w : Weirdℕ m}{v : Weirdℕ n} → Ren w v → Ren (T w) (T v)
⋆lift ρ (T x) = T (ρ x)

ren : ∀{m n}{w : Weirdℕ m}{v : Weirdℕ n} → Ren⋆ m n → Ren w v → ScopedTm w
  → ScopedTm v
renT : ∀{m n o}{w : Weirdℕ m}{v : Weirdℕ n} → Ren⋆ m n → Ren w v
  → Tel w o → Tel v o

ren-List : ∀{m n}{w : Weirdℕ m}{v : Weirdℕ n} → Ren⋆ m n → Ren w v 
         → List (ScopedTm w)
         → List (ScopedTm v)
ren-List ρ⋆ ρ [] = []
ren-List ρ⋆ ρ (x ∷ xs) = (ren ρ⋆ ρ x) ∷ (ren-List ρ⋆ ρ xs)

ren ρ⋆ ρ (` x) = ` (ρ x)
ren ρ⋆ ρ (Λ K t) = Λ K (ren (lift⋆ ρ⋆) (⋆lift ρ) t) 
ren ρ⋆ ρ (t ·⋆ A) = ren ρ⋆ ρ t ·⋆ ren⋆ ρ⋆ A
ren ρ⋆ ρ (ƛ A t)  = ƛ (ren⋆ ρ⋆ A) (ren ρ⋆ (lift ρ) t)
ren ρ⋆ ρ (t · u) = ren ρ⋆ ρ t · ren ρ⋆ ρ u
ren ρ⋆ ρ (con c) = con c
ren ρ⋆ ρ (error A) = error (ren⋆ ρ⋆ A)
ren ρ⋆ ρ (builtin b) = builtin b
ren ρ⋆ ρ (wrap A B t) = wrap (ren⋆ ρ⋆ A) (ren⋆ ρ⋆ B) (ren ρ⋆ ρ t)
ren ρ⋆ ρ (unwrap t) = unwrap (ren ρ⋆ ρ t)
ren ρ⋆ ρ (constr A i cs) =  constr (ren⋆ ρ⋆ A) i (ren-List ρ⋆ ρ cs) 
ren ρ⋆ ρ (case A x cs) = case (ren⋆ ρ⋆ A) (ren ρ⋆ ρ  x) (ren-List ρ⋆ ρ cs)

renT ρ⋆ ρ []       = []
renT ρ⋆ ρ (t ∷ ts) = ren ρ⋆ ρ t ∷ renT ρ⋆ ρ ts

-- substitution
Sub⋆ : ℕ → ℕ → Set
Sub⋆ m n = Fin m → ScopedTy n

slift⋆ : ∀{m n} → Sub⋆ m n → Sub⋆ (suc m) (suc n)
slift⋆ ρ zero    = ` zero
slift⋆ ρ (suc α) = ren⋆ suc (ρ α)

sub⋆ : ∀{m n} → Sub⋆ m n → ScopedTy m → ScopedTy n

sub⋆-List : ∀{m n} → Sub⋆ m n → List (ScopedTy m) → List (ScopedTy n)
sub⋆-List σ [] = []
sub⋆-List σ (x ∷ xs) = (sub⋆ σ x) ∷ (sub⋆-List σ xs)

sub⋆-ListList : ∀{m n} → Sub⋆ m n → List (List (ScopedTy m)) → List (List (ScopedTy n))
sub⋆-ListList σ [] = []
sub⋆-ListList σ (xs ∷ xss) = (sub⋆-List σ xs) ∷ (sub⋆-ListList σ xss)

sub⋆ σ (` α)   = σ α
sub⋆ σ (A ⇒ B) = sub⋆ σ A ⇒ sub⋆ σ B
sub⋆ σ (Π K A) = Π K (sub⋆ (slift⋆ σ) A)
sub⋆ σ (ƛ K A) = ƛ K (sub⋆ (slift⋆ σ) A)
sub⋆ σ (A · B) = sub⋆ σ A · sub⋆ σ B
sub⋆ σ (con c) = con c
sub⋆ σ (μ A B) = μ (sub⋆ σ A) (sub⋆ σ B)
sub⋆ σ (SOP xss) = SOP (sub⋆-ListList σ xss) 

sub⋆T : ∀{m n o} → Sub⋆ m n → Tel⋆ m o → Tel⋆ n o
sub⋆T σ⋆ []       = []
sub⋆T σ⋆ (A ∷ As) = sub⋆ σ⋆ A ∷ sub⋆T σ⋆ As

Sub : ∀{m n} → Weirdℕ m → Weirdℕ n → Set
Sub v w = WeirdFin v → ScopedTm w

slift : ∀{m n}{w : Weirdℕ m}{v : Weirdℕ n} → Sub v w → Sub (S v) (S w)
slift σ Z     = ` Z
slift σ (S x) = ren id S (σ x)

⋆slift : ∀{m n}{w : Weirdℕ m}{v : Weirdℕ n} → Sub w v → Sub (T w) (T v)
⋆slift σ (T x) = ren suc T (σ x)

sub : ∀{m n}{v : Weirdℕ m}{w : Weirdℕ n} → Sub⋆ m n → Sub v w
  → ScopedTm v → ScopedTm w
subT : ∀{m n o}{v : Weirdℕ m}{w : Weirdℕ n} → Sub⋆ m n → Sub v w
  → Tel v o → Tel w o

sub-List : ∀{m n}{v : Weirdℕ m}{w : Weirdℕ n} → Sub⋆ m n → Sub v w
  → List (ScopedTm v) → List (ScopedTm w)
sub-List σ⋆ σ [] = []
sub-List σ⋆ σ (x ∷ xs) = (sub σ⋆ σ x) ∷ (sub-List σ⋆ σ xs)

sub σ⋆ σ (` x) = σ x
sub σ⋆ σ (Λ K t) = Λ K (sub (slift⋆ σ⋆) (⋆slift σ) t)
sub σ⋆ σ (t ·⋆ A) = sub σ⋆ σ t ·⋆ sub⋆ σ⋆ A
sub σ⋆ σ (ƛ A t) = ƛ (sub⋆ σ⋆ A) (sub σ⋆ (slift σ) t)
sub σ⋆ σ (t · u) = sub σ⋆ σ t · sub σ⋆ σ u
sub σ⋆ σ (con c) = con c
sub σ⋆ σ (error A) = error (sub⋆ σ⋆ A)
sub σ⋆ σ (builtin b) = builtin b
sub σ⋆ σ (wrap A B t) = wrap (sub⋆ σ⋆ A) (sub⋆ σ⋆ B) (sub σ⋆ σ t)
sub σ⋆ σ (unwrap t) = unwrap (sub σ⋆ σ t)
sub σ⋆ σ (constr A i cs) = constr (sub⋆ σ⋆ A) i (sub-List σ⋆ σ cs)
sub σ⋆ σ (case A x cs) = case (sub⋆ σ⋆ A) (sub σ⋆ σ x) (sub-List σ⋆ σ cs)


subT σ⋆ σ []       = []
subT σ⋆ σ (t ∷ ts) = sub σ⋆ σ t ∷ subT σ⋆ σ ts

ext : ∀{m n}{v : Weirdℕ m}{w : Weirdℕ n} → Sub v w → ScopedTm w → Sub (S v) w
ext σ t Z = t
ext σ t (S x) = σ x

⋆ext : ∀{m n}{v : Weirdℕ m}{w : Weirdℕ n} → Sub v w → Sub (T v) w
⋆ext σ (T x) = σ x

ext⋆ : ∀{m n} → Sub⋆ m n → ScopedTy n → Sub⋆ (suc m) n
ext⋆ σ A zero = A
ext⋆ σ A (suc α) = σ α

_[_] : ∀{n}{v : Weirdℕ n} → ScopedTm (S v) → ScopedTm v → ScopedTm v
t [ u ] = sub ` (ext ` u) t

_[_]⋆ : ∀{n}{w : Weirdℕ n} → ScopedTm (T w) → ScopedTy n → ScopedTm w
t [ A ]⋆ = sub (ext⋆ ` A) (⋆ext `) t
```

# Proofs

```
lift⋆-cong : ∀{m n}{ρ ρ' : Ren⋆ m n}
  → (∀ x → ρ x ≡ ρ' x)
  → ∀ x → lift⋆ ρ x ≡ lift⋆ ρ' x
lift⋆-cong p zero    = refl
lift⋆-cong p (suc x) = cong suc (p x)

ren⋆-cong : ∀{m n}{ρ ρ' : Ren⋆ m n}
  → (∀ x → ρ x ≡ ρ' x)
  → ∀ x → ren⋆ ρ x ≡ ren⋆ ρ' x

ren⋆-cong-List :  ∀{m n}{ρ ρ' : Ren⋆ m n}
  → (∀ x → ρ x ≡ ρ' x) 
  → ∀ xs → ren⋆-List ρ xs ≡ ren⋆-List ρ' xs
ren⋆-cong-List p [] = refl
ren⋆-cong-List p (x ∷ xs) = cong₂ _∷_ (ren⋆-cong p x) (ren⋆-cong-List p xs)

ren⋆-cong-ListList : ∀ {m n} {ρ ρ' : Ren⋆ m n}
  → (∀ x → ρ x ≡ ρ' x)
  → ∀ xss → ren⋆-ListList ρ xss ≡ ren⋆-ListList ρ' xss
ren⋆-cong-ListList p [] = refl
ren⋆-cong-ListList p (xs ∷ xss) = cong₂ _∷_ (ren⋆-cong-List p xs) (ren⋆-cong-ListList p xss)

ren⋆-cong p (` x)       = cong ` (p x)
ren⋆-cong p (A ⇒ B)     = cong₂ _⇒_ (ren⋆-cong p A) (ren⋆-cong p B)
ren⋆-cong p (Π K A)     = cong (Π K) (ren⋆-cong (lift⋆-cong p) A)
ren⋆-cong p (ƛ K A)     = cong (ƛ K) (ren⋆-cong (lift⋆-cong p) A)
ren⋆-cong p (A · B)     = cong₂ _·_ (ren⋆-cong p A) (ren⋆-cong p B)
ren⋆-cong p (con c)     = refl
ren⋆-cong p (μ pat arg) = cong₂ μ (ren⋆-cong p pat) (ren⋆-cong p arg)
ren⋆-cong p (SOP xss)   = cong SOP (ren⋆-cong-ListList p xss)

slift⋆-cong : ∀{m n}{ρ ρ' : Sub⋆ m n}
  → (∀ x → ρ x ≡ ρ' x)
  → ∀ x → slift⋆ ρ x ≡ slift⋆ ρ' x
slift⋆-cong p zero    = refl
slift⋆-cong p (suc x) = cong (ren⋆ suc) (p x) 

sub⋆-cong : ∀{m n}{σ σ' : Sub⋆ m n}
  → (∀ x → σ x ≡ σ' x)
  → ∀ x → sub⋆ σ x ≡ sub⋆ σ' x

sub⋆-cong-List :  ∀{m n}{σ σ' : Sub⋆ m n}
  → (∀ x → σ x ≡ σ' x)
  → ∀ xs → sub⋆-List σ xs ≡ sub⋆-List σ' xs
sub⋆-cong-List p [] = refl
sub⋆-cong-List p (x ∷ xs) = cong₂ _∷_ (sub⋆-cong p x) (sub⋆-cong-List p xs)

sub⋆-cong-ListList : ∀{m n}{σ σ' : Sub⋆ m n}
  → (∀ x → σ x ≡ σ' x)
  → ∀ xss → sub⋆-ListList σ xss ≡ sub⋆-ListList σ' xss
sub⋆-cong-ListList p [] = refl
sub⋆-cong-ListList p (xs ∷ xss) = cong₂ _∷_ (sub⋆-cong-List p xs) (sub⋆-cong-ListList p xss)

sub⋆-cong p (` x)       = p x
sub⋆-cong p (A ⇒ B)     = cong₂ _⇒_ (sub⋆-cong p A) (sub⋆-cong p B)
sub⋆-cong p (Π K A)     = cong (Π K) (sub⋆-cong (slift⋆-cong p) A)
sub⋆-cong p (ƛ K A)     = cong (ƛ K) (sub⋆-cong (slift⋆-cong p) A)
sub⋆-cong p (A · B)     = cong₂ _·_ (sub⋆-cong p A) (sub⋆-cong p B)
sub⋆-cong p (con c)     = refl 
sub⋆-cong p (μ pat arg) = cong₂ μ (sub⋆-cong p pat) (sub⋆-cong p arg)
sub⋆-cong p (SOP xss)   = cong SOP (sub⋆-cong-ListList p xss)

sub-cons : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'} → Sub w w' → ScopedTm w' →
  Sub (S w) w'
sub-cons σ t Z     = t
sub-cons σ t (S x) = σ x  

sub-cons⋆ : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'} → Sub w w' → Sub (T w) w'
sub-cons⋆ σ (T x) = σ x

```
