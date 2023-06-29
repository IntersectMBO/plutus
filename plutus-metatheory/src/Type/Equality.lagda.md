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
open import Data.Vec using (Vec;[];_∷_)
open import Data.List using (List;[];_∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym)

open import Utils using (*;♯;J;K)
open import Type using (Ctx⋆;_,⋆_;Φ;Ψ;_⊢⋆_;A;A';B;B';C)
open _⊢⋆_
open import Type.RenamingSubstitution 
   using (_[_];Ren;ren;Sub;sub;ext;sub-ren;ren-sub;sub-cong;ren-sub-cons;exts;sub-comp)
   using (sub-sub-cons;ren-List;ren-VecList;sub-List;sub-VecList)
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
data _[≡]β_ : List (Φ ⊢⋆ *) → List (Φ ⊢⋆ *) → Set
data _⟨[≡]⟩β_ : ∀{n} → Vec (List (Φ ⊢⋆ *)) n → Vec (List (Φ ⊢⋆ *)) n → Set

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

  con≡β : ∀{c c' : Φ ⊢⋆ ♯}
        → c ≡β c'
          -----------
        → con c ≡β con c'
  
  SOP≡β : ∀{n}{xss xss' : Vec (List (Φ ⊢⋆ *)) n}
        → xss ⟨[≡]⟩β xss'
         ---------------
        → SOP xss ≡β SOP xss'
  -- computation rule

  β≡β : (B : Φ ,⋆ J ⊢⋆ K)
      → (A : Φ ⊢⋆ J)
        ------------------
      → ƛ B · A ≡β B [ A ]

data _[≡]β_ where 
  nil[≡]β : _[≡]β_ {Φ} [] []

  cons[≡]β : ∀{A A' : Φ ⊢⋆ *}{AS AS' : List (Φ ⊢⋆ *)}
           → A ≡β A'
           → AS [≡]β AS'
             ----------------
           → (A ∷ AS) [≡]β (A' ∷ AS')

data _⟨[≡]⟩β_ where 
  nil⟨[≡]⟩β : _⟨[≡]⟩β_ {Φ} [] []

  cons⟨[≡]⟩β : ∀{n}{AS AS' : List (Φ ⊢⋆ *)}{ASS ASS' : Vec (List (Φ ⊢⋆ *)) n}
           → AS [≡]β AS'
           → ASS ⟨[≡]⟩β ASS'
             ----------------
           → (AS ∷ ASS) ⟨[≡]⟩β (AS' ∷ ASS')
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
ren≡β-List : ∀{AS BS}(ρ : Ren Φ Ψ)
      → AS [≡]β BS
        ------------------
      → ren-List ρ AS [≡]β ren-List ρ BS
ren≡β-VecList : ∀{n}{ASS BSS : Vec (List (Φ ⊢⋆ *)) n}(ρ : Ren Φ Ψ)
      → ASS ⟨[≡]⟩β BSS
        ------------------
      → ren-VecList ρ ASS ⟨[≡]⟩β ren-VecList ρ BSS

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
ren≡β ρ (con≡β p)     = con≡β (ren≡β ρ p)
ren≡β ρ (SOP≡β p)   = SOP≡β (ren≡β-VecList ρ p)

ren≡β-List ρ nil[≡]β = nil[≡]β
ren≡β-List ρ (cons[≡]β x p) = cons[≡]β (ren≡β ρ x) (ren≡β-List ρ p)
ren≡β-VecList ρ nil⟨[≡]⟩β = nil⟨[≡]⟩β
ren≡β-VecList ρ (cons⟨[≡]⟩β x p) = cons⟨[≡]⟩β (ren≡β-List ρ x) (ren≡β-VecList ρ p) 
```

## Substitution for proofs of type equality

```
sub≡β : (σ : Sub Φ Ψ)
      → A ≡β B
        ------------------
      → sub σ A ≡β sub σ B
sub≡β-List : ∀{AS BS}(σ : Sub Φ Ψ)
      → AS [≡]β BS
        ------------------
      → sub-List σ AS [≡]β sub-List σ BS

sub≡β-VecList : ∀{n}{ASS BSS : Vec (List (Φ ⊢⋆ *)) n}(σ : Sub Φ Ψ)
      → ASS ⟨[≡]⟩β BSS
        ------------------
      → sub-VecList σ ASS ⟨[≡]⟩β sub-VecList σ BSS
  
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
sub≡β ρ (con≡β p)     = con≡β (sub≡β ρ p)
sub≡β σ (SOP≡β p)   = SOP≡β (sub≡β-VecList σ p) 

sub≡β-List σ nil[≡]β = nil[≡]β
sub≡β-List σ (cons[≡]β x xs) = cons[≡]β (sub≡β σ x) (sub≡β-List σ xs)
sub≡β-VecList σ nil⟨[≡]⟩β = nil⟨[≡]⟩β
sub≡β-VecList σ (cons⟨[≡]⟩β x p) = cons⟨[≡]⟩β (sub≡β-List σ x) (sub≡β-VecList σ p)     
```

