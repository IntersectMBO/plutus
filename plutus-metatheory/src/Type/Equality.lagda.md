---
title: Type Equality
layout: page
---

```
module Type.Equality where
```

## Fixity

```
infix  1 _≡β_
```

## Imports

```
open import Type
open import Type.RenamingSubstitution
open import Builtin.Constant.Type

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)
```

## Beta equality relation for types

This serves as a declaritive specification of the semantics of types.

We need to give constructors for reflexivity, symmetry and
transitivity as the presence of the beta-rule prevents these
properties from being derivable. We have congruence rules for all
constructors of type (except variables as this is subsumed by
reflexivity). Finally, we have one computation rule: the beta-rule for
application.

```
data _≡β_ : Φ ⊢⋆ J → Φ ⊢⋆ J → Set where

  -- structural rules

  refl≡β : (A : Φ ⊢⋆ J)
           ------------
         → A ≡β A
    
  sym≡β : A ≡β B
          ------
        → B ≡β A

  trans≡β : A ≡β B
          → B ≡β C
            ------
          → A ≡β C

  -- congruence rules

  -- (no variable rule is needed)
 
  ⇒≡β : A ≡β A'
      → B ≡β B'
        -----------------
      → A ⇒ B ≡β A' ⇒ B'
    
  Π≡β : B ≡β B'
        -----------
      → Π B ≡β Π B'
    
  ƛ≡β : B ≡β B'
        -----------
      → ƛ B ≡β ƛ B'
    
  ·≡β : A ≡β A'
      → B ≡β B'
        --------------------
      → A · B ≡β A' · B'
    
  μ≡β : A ≡β A'
      → B ≡β B'
        ----------------
      → μ A B ≡β μ A' B'
    
  -- computation rule

  β≡β : (B : Φ ,⋆ J ⊢⋆ K)
      → (A : Φ ⊢⋆ J)
        ------------------
      → ƛ B · A ≡β B [ A ]
    
```

```
≡2β : A ≡ A' → A ≡β A'
≡2β refl = refl≡β _
```

## Renaming for proofs of type equality

```
ren≡β : (ρ : Ren Φ Ψ)
      → A ≡β B
        ------------------
      → ren ρ A ≡β ren ρ B
ren≡β ρ (refl≡β A)    = refl≡β (ren ρ A)
ren≡β ρ (sym≡β p)     = sym≡β (ren≡β ρ p)
ren≡β ρ (trans≡β p q) = trans≡β (ren≡β ρ p) (ren≡β ρ q)
ren≡β ρ (⇒≡β p q)     = ⇒≡β (ren≡β ρ p) (ren≡β ρ q)
ren≡β ρ (Π≡β p)       = Π≡β (ren≡β (ext ρ) p)
ren≡β ρ (ƛ≡β p)       = ƛ≡β (ren≡β (ext ρ) p)
ren≡β ρ (·≡β p q)     = ·≡β (ren≡β ρ p) (ren≡β ρ q)
ren≡β ρ (μ≡β p q)     = μ≡β (ren≡β ρ p) (ren≡β ρ q)
ren≡β ρ (β≡β B A)     = trans≡β
  (β≡β _ _)
  (≡2β (trans (sym (sub-ren B))
              (trans (sub-cong (ren-sub-cons ρ A) B)
                     (ren-sub B))))
```

## Substitution for proofs of type equality

```
sub≡β : (σ : Sub Φ Ψ)
      → A ≡β B
        ------------------
      → sub σ A ≡β sub σ B
sub≡β σ (refl≡β A)    = refl≡β (sub σ A)
sub≡β σ (sym≡β p)     = sym≡β (sub≡β σ p)
sub≡β σ (trans≡β p q) = trans≡β (sub≡β σ p) (sub≡β σ q) 
sub≡β σ (⇒≡β p q)     = ⇒≡β (sub≡β σ p) (sub≡β σ q)
sub≡β σ (Π≡β p)       = Π≡β (sub≡β (exts σ) p)
sub≡β σ (ƛ≡β p)       = ƛ≡β (sub≡β (exts σ) p)
sub≡β σ (·≡β p q)     = ·≡β (sub≡β σ p) (sub≡β σ q)
sub≡β σ (μ≡β p q)     = μ≡β (sub≡β σ p) (sub≡β σ q)
sub≡β σ (β≡β B A)     = trans≡β
  (β≡β _ _)
  (≡2β (trans (trans (sym (sub-comp B))
                     (sub-cong (sub-sub-cons σ A) B))
              (sub-comp B)))
```

