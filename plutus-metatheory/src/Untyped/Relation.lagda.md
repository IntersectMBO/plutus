---
title: Untyped.Relation
layout: page
---

```
module Untyped.Relation where
open import Function using (case_of_)

open import Untyped
open import Data.Nat using (suc)
open import Data.Fin using (Fin)
open import Data.List hiding (fromMaybe)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (∃; _,_)
open import Relation.Nullary using (Dec; yes; no)

open import Untyped.Relation.Core public
open import Untyped.Relation.Properties public
open import Untyped.Relation.Pointwise public
```



This allows you to build relations modularly:

```
infixr 5 _+_

data _+_ (F G : RelationT) (@++ R : Relation) : Relation where
  inl : ∀ {X} {M N : X ⊢} → F R M N → (F + G) R M N
  inr : ∀ {X} {M N : X ⊢} → G R M N → (F + G) R M N

data Fix (F : RelationT) : Relation where
  fix : ∀ {X} {M N : X ⊢} → F (Fix F) M N → (Fix F) M N

Empty : RelationT
Empty R M N = ⊥

Const : @++ Relation → RelationT
Const R _ = R
```

## Running relations

A function that by construction refines R:

```
Refinement? : Relation → Set
Refinement? R =
  ∀ {X}
  → (M : X ⊢)
  → Maybe (∃ (λ M' → R M M'))

refine? : ∀ {X} {R : Relation} → Refinement? R → X ⊢ → Maybe (X ⊢)
refine? f M with f M
... | nothing = nothing
... | just (M' , _) = just M'

refine?-refines :
  ∀ {R : Relation}
  → (f : Refinement? R)
  → Refines? (refine? f) R
refine?-refines f M _ fM≡just with f M | fM≡just
... | just ( _ , RMN) | refl = RMN
```

For relation transformers, we can run the first, and if it fails the second:

```
infixr 5 _<|>_
_<|>_ :
  ∀ {F G : RelationT} {R : Relation}
  → Refinement? (F R)
  → Refinement? (G R)
  → Refinement? ((F + G) R)
(f <|> g) M
  with f M
... | just (N , RMN) = just (N , inl RMN)
... | nothing
  with g M
... | just (N , SMN) = just (N , inr SMN)
... | nothing = nothing
```


## Structures

```
record Equivalence (_~_ : Relation) : Set where
  field
    ~-refl : Reflexive _~_
    ~-trans : Transitive _~_
    ~-sym : Symmetric _~_

record TermCompatible (_~_ : Relation) : Set where
  field
    compat-var : ∀ {X} {n : Fin X} → ` n  ~ ` n
    compat-ƛ : ∀ {X} {M N : suc X ⊢} → M ~ N → ƛ M ~ ƛ N
    compat-· : Compatible₂ _~_ _·_
    compat-force : Compatible _~_ force
    compat-delay : Compatible _~_ delay
    compat-constr :
      ∀ {X i} {Ms Ns : List (X ⊢)} →
        Pointwise _~_ Ms Ns →
        constr i Ms ~ constr i Ns
    compat-case :
      ∀ {X} {M N : X ⊢} {Ms Ns} →
        M ~ N →
        Pointwise _~_ Ms Ns →
        case M Ms ~ case N Ns
    compat-con : ∀ {k X} → con {X} k ~ con {X} k
    compat-builtin : ∀ {X} {f} → builtin {X} f ~ builtin {X} f
    compat-error : ∀ {X} → error {X} ~ error {X}
```
