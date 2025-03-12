---
title: Certificate
layout: page
---
# Certificates

## Produce a Proof, or a useful Counter Example
```
module VerifiedCompilation.Certificate where

open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary as Binary using (Decidable)
open import Level
open import Data.Product.Base using (_×_;_,_)
open import Untyped using (_⊢; error)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_;inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Data.List.Relation.Binary.Pointwise using (Pointwise-≡⇒≡; ≡⇒Pointwise-≡)

variable
  𝓁 : Level

data ProofOrCE (P : Set 𝓁) : Set (suc 𝓁) where
  proof : P → ProofOrCE P
  ce : {X X' : Set} → X → X' → ProofOrCE P

decToPCE : {X : Set} {P : Set} → Dec P → {before after : X} → ProofOrCE P
decToPCE (yes p) = proof p
decToPCE (no ¬p) {before} {after} = ce before after

MatchOrCE : {X X' : Set} {𝓁 : Level} → (P : X → X' → Set 𝓁) → Set (suc 𝓁)
MatchOrCE {X} {X'} P = (a : X) → (b : X') → ProofOrCE (P a b)

matchOrCE : {X X' : Set} {𝓁 : Level} → {P : X → X' → Set 𝓁} → Binary.Decidable P → MatchOrCE P
matchOrCE P a b with P a b
... | yes p = proof p
... | no _ = ce a b

pcePointwise : {X X' : Set} {𝓁 : Level} → {P : X → X' → Set 𝓁} → MatchOrCE P → MatchOrCE (Pointwise P)
pcePointwise isP? [] [] = proof Pointwise.[]
pcePointwise {X = X} isP? [] ys = ce {X = List X} [] ys
pcePointwise {X' = X'} isP? xs [] = ce {X' = List X'} xs []
pcePointwise isP? (x ∷ xs) (y ∷ ys) with isP? x y
... | ce b a = ce b a
... | proof p with pcePointwise isP? xs ys
...   | ce b a = ce b a
...   | proof ps = proof (p Pointwise.∷ ps)
```
