---
title: Certificate
layout: page
---
# Certificates

## Produce a Proof, or a useful Counter Example
```
module VerifiedCompilation.Certificate where

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Level
open import Data.Product.Base using (_×_;_,_)
open import Untyped using (_⊢; error)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_;inj₁; inj₂)

variable
  𝓁 : Level

data ProofOrCE (P : Set 𝓁) : Set (suc 𝓁) where
  proof : P → ProofOrCE P
  ce : {X X' : Set} → X → X' → ProofOrCE P

{-
_×-pce_ : {P : Set} {Q : Set} → ProofOrCE P → ProofOrCE Q → (ProofOrCE P) ⊎ (ProofOrCE Q) ⊎ (ProofOrCE (P × Q))
proof x₁ ×-pce proof x₂ = inj₂ (inj₂ (proof (x₁ , x₂)))
proof x₁ ×-pce ce before after = inj₂ (inj₁ (ce (before) (after)))
ce before after ×-pce _ = inj₁ (ce before after)
-}

decToPCE : {X : Set} {P : Set} → Dec P → {before after : X} → ProofOrCE P
decToPCE (yes p) = proof p
decToPCE (no ¬p) {before} {after} = ce before after

```
