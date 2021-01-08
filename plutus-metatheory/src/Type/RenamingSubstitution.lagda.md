---
title: Type Renaming and Substitution
layout: page
---

```
module Type.RenamingSubstitution where
```

## Imports

```
open import Type
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)
```

## Type renaming

A type renaming is a mapping of type variables to type variables.

```
Ren : Ctx⋆ → Ctx⋆ → Set
Ren Φ Ψ = ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J
```

Let `ρ` range of renamings.
```
variable
  ρ ρ' : Ren Φ Ψ
```

Extending a type renaming — used when going under a binder.

```
ext : Ren Φ Ψ
      -----------------------------
    → ∀ {K} → Ren (Φ ,⋆ K) (Ψ ,⋆ K)
ext ρ Z      =  Z
ext ρ (S α)  =  S (ρ α)
```

Apply a type renaming to a type.
```
ren : Ren Φ Ψ
      -----------------------
    → ∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J
ren ρ (` α)       = ` (ρ α)
ren ρ (Π B)       = Π (ren (ext ρ) B)
ren ρ (A ⇒ B)     = ren ρ A ⇒ ren ρ B
ren ρ (ƛ B)       = ƛ (ren (ext ρ) B)
ren ρ (A · B)     = ren ρ A · ren ρ B
ren ρ (μ A B)     = μ (ren ρ A) (ren ρ B)
ren ρ (con tcn) = con tcn
```

Weakening is a special case of renaming.

```
weaken : Φ ⊢⋆ J
         -----------
       → Φ ,⋆ K ⊢⋆ J
weaken = ren S
```

## Renaming proofs

First functor law for `ext`

```
ext-id : (α : Φ ,⋆ K ∋⋆ J)
         -----------------
       → ext id α ≡ α
ext-id Z     = refl
ext-id (S α) = refl
```

This congruence lemma and analogous ones for exts⋆, ren, and
subst⋆ avoids the use of extensionality when reasoning about equal
renamings/substitutions as we only need a pointwise version of
equality. If we used the standard library's cong we would need to
postulate extensionality and our equality proofs wouldn't compute. I
learnt this from Conor McBride.

```
ext-cong : (∀ {J}(α : Φ ∋⋆ J) → ρ α ≡ ρ' α)
         → ∀{J K}(α : Φ ,⋆ J ∋⋆ K)
           --------------------------------
         → ext ρ α ≡ ext ρ' α
ext-cong p Z     = refl
ext-cong p (S α) = cong S (p α)
```

Congruence lemma for `ren`

```
ren-cong : (∀ {J}(α : Φ ∋⋆ J) → ρ α ≡ ρ' α)
         → ∀{K}(A : Φ ⊢⋆ K)
           --------------------------------
         → ren ρ A ≡ ren ρ' A
ren-cong p (` α)   = cong ` (p α)
ren-cong p (Π A)   = cong Π (ren-cong (ext-cong p) A)
ren-cong p (A ⇒ B) = cong₂ _⇒_ (ren-cong p A) (ren-cong p B)
ren-cong p (ƛ A)   = cong ƛ (ren-cong (ext-cong p) A)
ren-cong p (A · B) = cong₂ _·_ (ren-cong p A) (ren-cong p B)
ren-cong p (μ A B) = cong₂ μ (ren-cong p A) (ren-cong p B)
ren-cong p (con c) = refl
```

First functor law for `ren`

```
ren-id : (t : Φ ⊢⋆ J)
         ------------
       → ren id t ≡ t
ren-id (` α)     = refl
ren-id (Π A)     = cong Π (trans (ren-cong ext-id A) (ren-id A))
ren-id (A ⇒ B)   = cong₂ _⇒_(ren-id A) (ren-id B)
ren-id (ƛ A)     = cong ƛ (trans (ren-cong ext-id A) (ren-id A))
ren-id (A · B)   = cong₂ _·_ (ren-id A) (ren-id B)
ren-id (μ A B)   = cong₂ μ (ren-id A) (ren-id B)
ren-id (con tcn) = refl
```

Second functor law for `ext`

```
ext-comp : ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
           ---------------------------------
         → ext (ρ ∘ ρ') x ≡ ext ρ (ext ρ' x)
ext-comp Z     = refl
ext-comp (S x) = refl
```

Second functor law for `ren`

```
ren-comp : ∀{J}(A : Φ ⊢⋆ J)
           ---------------------------------
         → ren (ρ ∘ ρ') A ≡ ren ρ (ren ρ' A)
ren-comp (` x)     = refl
ren-comp (Π A)     = cong Π (trans (ren-cong ext-comp A) (ren-comp A))
ren-comp (A ⇒ B)   = cong₂ _⇒_ (ren-comp A) (ren-comp B)
ren-comp (ƛ A)     = cong ƛ (trans (ren-cong ext-comp A) (ren-comp A))
ren-comp (A · B)   = cong₂ _·_ (ren-comp A) (ren-comp B)
ren-comp (μ A B)   = cong₂ μ (ren-comp A) (ren-comp B)
ren-comp (con tcn) = refl
```

## Type substitution

A type substitution is a mapping of type variables to types.

```
Sub : Ctx⋆ → Ctx⋆ → Set
Sub Φ Ψ = ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J
```

Let `σ` range over substitutions:
```
variable
  σ σ' : Sub Φ Ψ
```

Extending a type substitution — used when going under a binder.

```
exts : Sub Φ Ψ
       -----------------------------
     → ∀ {K} → Sub (Φ ,⋆ K) (Ψ ,⋆ K)
exts σ Z      = ` Z
exts σ (S α)  = weaken (σ α)
```

Apply a type substitution to a type.

```
sub : Sub Φ Ψ
      -----------------------
    → ∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J
sub σ (` α)       = σ α
sub σ (Π B)       = Π (sub (exts σ) B)
sub σ (A ⇒ B)     = sub σ A ⇒ sub σ B
sub σ (ƛ B)       = ƛ (sub (exts σ) B)
sub σ (A · B)     = sub σ A · sub σ B
sub σ (μ A B)     = μ (sub σ A) (sub σ B)
sub σ (con tcn)   = con tcn
```

Extend a substitution with an additional type (analogous to `cons` for
backward lists)

```
sub-cons : Sub Φ Ψ
         → ∀{J}(A : Ψ ⊢⋆ J)
           ----------------
         → Sub (Φ ,⋆ J) Ψ
sub-cons f A Z = A
sub-cons f A (S x) = f x
```

A special case is substitution a type for the outermost free variable:
```
_[_] : Φ ,⋆ K ⊢⋆ J
     → Φ ⊢⋆ K 
       -----------
     → Φ ⊢⋆ J
B [ A ] =  sub (sub-cons ` A) B
```

## Type Substitution Proofs

Extending the identity substitution yields the identity substitution

```
exts-id : (α : Φ ,⋆ K ∋⋆ J)
          -----------------
        → exts ` α ≡ ` α 
exts-id Z     = refl
exts-id (S α) = refl
```

Congruence lemma for `exts`

```
exts-cong : (∀ {J}(α : Φ ∋⋆ J) → σ α ≡ σ' α)
          → ∀{J K}(α : Φ ,⋆ K ∋⋆ J)
            --------------------------------
          → exts σ α ≡ exts σ' α
exts-cong p Z     = refl
exts-cong p (S α) = cong (ren S) (p α)
```

Congruence lemma for `sub`

```
sub-cong : (∀ {J}(α : Φ ∋⋆ J) → σ α ≡ σ' α)
         → ∀{K}(A : Φ ⊢⋆ K)
           -------------------------------
         → sub σ A ≡ sub σ' A
sub-cong p (` α)       = p α
sub-cong p (Π A)       = cong Π (sub-cong (exts-cong p) A)
sub-cong p (A ⇒ B)     = cong₂ _⇒_ (sub-cong p A) (sub-cong p B)
sub-cong p (ƛ A)       = cong ƛ (sub-cong (exts-cong p) A)
sub-cong p (A · B)     = cong₂ _·_ (sub-cong p A) (sub-cong p B)
sub-cong p (μ A B)     = cong₂ μ (sub-cong p A) (sub-cong p B)
sub-cong p (con tcn)   = refl
```

First relative monad `law` for `sub`

```
sub-id : (t : Φ ⊢⋆ J)
         ------------
       → sub ` t ≡ t
sub-id (` α)      = refl
sub-id (Π A)      = cong Π (trans (sub-cong exts-id A) (sub-id A))
sub-id (A ⇒ B)    = cong₂ _⇒_ (sub-id A) (sub-id B)
sub-id (ƛ A)      = cong ƛ (trans (sub-cong exts-id A) (sub-id A))
sub-id (A · B)    = cong₂ _·_ (sub-id A) (sub-id B)
sub-id (μ A B)    = cong₂ μ (sub-id A) (sub-id B)
sub-id (con tcn)  = refl
```

Fusion of `exts` and `ext`

```
exts-ext : ∀{J K}(α : Φ ,⋆ K ∋⋆ J)
           ---------------------------------
         → exts (σ ∘ ρ) α ≡ exts σ (ext ρ α)
exts-ext Z     = refl
exts-ext (S α) = refl
```

Fusion for `sub` and `ren`

```
sub-ren : ∀{J}(A : Φ ⊢⋆ J)
          -------------------------------
        → sub (σ ∘ ρ) A ≡ sub σ (ren ρ A)
sub-ren (` α)     = refl
sub-ren (Π A)     = cong Π (trans (sub-cong exts-ext A) (sub-ren A))
sub-ren (A ⇒ B)   = cong₂ _⇒_ (sub-ren A) (sub-ren B)
sub-ren (ƛ A)     = cong ƛ (trans (sub-cong exts-ext A) (sub-ren A))
sub-ren (A · B)   = cong₂ _·_ (sub-ren A) (sub-ren B)
sub-ren (μ A B)   = cong₂ μ (sub-ren A) (sub-ren B)
sub-ren (con tcn) = refl
```

Fusion for `exts` and `ext`

```
ren-ext-exts : ∀{J K}(α : Φ ,⋆ K ∋⋆ J)
               -------------------------------------------
             → exts (ren ρ ∘ σ) α ≡ ren (ext ρ) (exts σ α)
ren-ext-exts Z     = refl
ren-ext-exts (S α) = trans (sym (ren-comp _)) (ren-comp _)
```

Fusion for `ren` and `sub`

```
ren-sub : ∀{J}(A : Φ ⊢⋆ J)
          -----------------------------------
        → sub (ren ρ ∘ σ) A ≡ ren ρ (sub σ A)
ren-sub (` α)     = refl
ren-sub (Π A)     = cong Π (trans (sub-cong ren-ext-exts  A) (ren-sub A))
ren-sub (A ⇒ B)   = cong₂ _⇒_ (ren-sub A) (ren-sub B)
ren-sub (ƛ A)     = cong ƛ (trans (sub-cong ren-ext-exts A) (ren-sub A))
ren-sub (A · B)   = cong₂ _·_ (ren-sub A) (ren-sub B)
ren-sub (μ A B)   = cong₂ μ (ren-sub A) (ren-sub B)
ren-sub (con tcn) = refl
```

Fusion of two `exts`

```
extscomp : ∀{J K}(α : Φ ,⋆ K ∋⋆ J)
           ------------------------------------------------
         → exts (sub σ ∘ σ') α ≡ sub (exts σ) (exts σ' α)
extscomp         Z     = refl
extscomp {σ' = σ'} (S α) = trans (sym (ren-sub (σ' α))) (sub-ren (σ' α))
```

Fusion of substitutions/third relative monad law for `sub`

```
sub-comp : ∀{J}(A : Φ ⊢⋆ J)
           -------------------------------------
         → sub (sub σ ∘ σ') A ≡ sub σ (sub σ' A)
sub-comp (` x)     = refl
sub-comp (Π A)     = cong Π (trans (sub-cong extscomp A) (sub-comp A))
sub-comp (A ⇒ B)   = cong₂ _⇒_ (sub-comp A) (sub-comp B)
sub-comp (ƛ A)     = cong ƛ (trans (sub-cong extscomp A) (sub-comp A))
sub-comp (A · B)   = cong₂ _·_ (sub-comp A) (sub-comp B)
sub-comp (μ A B)   = cong₂ μ (sub-comp A) (sub-comp B)
sub-comp (con tcn) = refl
```

Commuting `sub-cons` and `ren`

```
ren-sub-cons : (ρ : Ren Φ Ψ)
             → (A : Φ ⊢⋆ K)
             → (α : Φ ,⋆ K ∋⋆ J)
               -------------------------------------------------------
             → sub-cons ` (ren ρ A) (ext ρ α) ≡ ren ρ (sub-cons ` A α)
ren-sub-cons ρ A Z     = refl
ren-sub-cons ρ A (S α) = refl
```

Commuting `sub-cons` and `sub`

```
sub-sub-cons : (σ : Sub Φ Ψ)
             → (M : Φ ⊢⋆ K)
             → (α : Φ ,⋆ K ∋⋆ J)
               --------------------------------------------------------------
             → sub (sub-cons ` (sub σ M)) (exts σ α) ≡ sub σ (sub-cons ` M α)
sub-sub-cons σ M Z     = refl
sub-sub-cons σ M (S α) = trans (sym (sub-ren (σ α))) (sub-id (σ α))
```

A useful lemma for fixing up the types when renaming a `wrap` or `unwrap`

```
ren-μ : (ρ⋆ : Ren Φ Ψ)
      → (A : Φ ⊢⋆ _)
      → (B : Φ ⊢⋆ K)
      → -----------------------------------------------------
        ren ρ⋆ (A · ƛ (μ (weaken A) (` Z)) · B)
        ≡
        ren ρ⋆ A · ƛ (μ (weaken (ren ρ⋆ A)) (` Z)) · ren ρ⋆ B
ren-μ ρ⋆ A B = cong
  (λ X → ren ρ⋆ A · ƛ (μ X (` Z)) · ren ρ⋆ B)
  (trans (sym (ren-comp A)) (ren-comp A))
```

A useful lemma for fixing up the types when substituting into a `wrap`
or `unwrap`

```
sub-μ : (σ⋆ : Sub Φ Ψ)
      → (A : Φ ⊢⋆ _)
      → (B : Φ ⊢⋆ K)
        -----------------------------------------------------
      → sub σ⋆ (A · ƛ (μ (weaken A) (` Z)) · B)
        ≡
        sub σ⋆ A · ƛ (μ (weaken (sub σ⋆ A)) (` Z)) · sub σ⋆ B
sub-μ σ⋆ A B = cong
  (λ X → sub σ⋆ A · ƛ (μ X (` Z)) · sub σ⋆ B)
  (trans (sym (sub-ren A)) (ren-sub A))
```
