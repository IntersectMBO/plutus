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

data SimplifierTag : Set where
  floatDelayT : SimplifierTag
  forceDelayT : SimplifierTag
  caseOfCaseT : SimplifierTag
  caseReduceT : SimplifierTag
  inlineT : SimplifierTag
  cseT : SimplifierTag

{-# FOREIGN GHC import UntypedPlutusCore.Transform.Simplifier #-}
{-# COMPILE GHC SimplifierTag = data SimplifierStage (FloatDelay | ForceDelay | CaseOfCase | CaseReduce | Inline | CSE) #-}

variable
  𝓁 : Level

data ProofOrCE (P : Set 𝓁) : Set (suc 𝓁) where
  proof : P → ProofOrCE P
  ce : {X X' : Set} → SimplifierTag → X → X' → ProofOrCE P

decToPCE : {X : Set} {P : Set} → SimplifierTag → Dec P → {before after : X} → ProofOrCE P
decToPCE _ (yes p) = proof p
decToPCE tag (no ¬p) {before} {after} = ce tag before after

MatchOrCE : {X X' : Set} {𝓁 : Level} → (P : X → X' → Set 𝓁) → Set (suc 𝓁)
MatchOrCE {X} {X'} P = (a : X) → (b : X') → ProofOrCE (P a b)

matchOrCE : {X X' : Set} {𝓁 : Level} → {P : X → X' → Set 𝓁} → SimplifierTag → Binary.Decidable P → MatchOrCE P
matchOrCE tag P a b with P a b
... | yes p = proof p
... | no _ = ce tag a b

pcePointwise : {X X' : Set} {𝓁 : Level} → {P : X → X' → Set 𝓁} → SimplifierTag → MatchOrCE P → MatchOrCE (Pointwise P)
pcePointwise tag isP? [] [] = proof Pointwise.[]
pcePointwise {X = X} tag isP? [] ys = ce {X = List X} tag [] ys
pcePointwise {X' = X'} tag isP? xs [] = ce {X' = List X'} tag xs []
pcePointwise tag isP? (x ∷ xs) (y ∷ ys) with isP? x y
... | ce tag b a = ce tag b a
... | proof p with pcePointwise tag isP? xs ys
...   | ce tag b a = ce tag b a
...   | proof ps = proof (p Pointwise.∷ ps)
```
