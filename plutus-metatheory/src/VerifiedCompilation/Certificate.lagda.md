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
  forceCaseDelayT : SimplifierTag
  caseOfCaseT : SimplifierTag
  caseReduceT : SimplifierTag
  inlineT : SimplifierTag
  cseT : SimplifierTag

{-# FOREIGN GHC import UntypedPlutusCore.Transform.Simplifier #-}
{-# COMPILE GHC SimplifierTag = data SimplifierStage (FloatDelay | ForceDelay | ForceCaseDelay | CaseOfCase | CaseReduce | Inline | CSE) #-}

variable
  𝓁 𝓂 𝓃 : Level

data ProofOrCE (P : Set (𝓂 ⊔ 𝓃)) : Set (suc (𝓂 ⊔ 𝓃)) where
  proof : (p : P) → ProofOrCE P
  ce : {X : Set 𝓂} {X' : Set 𝓃} (¬p : ¬ P) → SimplifierTag → X → X' → ProofOrCE P

decToPCE : {X : Set} {P : Set} → SimplifierTag → Dec P → {before after : X} → ProofOrCE P
decToPCE _ (yes p) = proof p
decToPCE tag (no ¬p) {before} {after} = ce ¬p tag before after

pceToDec : {P : Set (𝓂 ⊔ 𝓃)} → ProofOrCE {𝓂 = 𝓂} {𝓃 = 𝓃} P → Dec P
pceToDec (proof p) = yes p
pceToDec (ce ¬p _ _ _) = no ¬p

MatchOrCE : {X : Set 𝓂} {X' : Set 𝓃} → (P : X → X' → Set (𝓂 ⊔ 𝓃)) → Set (suc (𝓂 ⊔ 𝓃))
MatchOrCE {𝓂 = 𝓂} {𝓃 = 𝓃} {X = X} {X' = X'} P = (a : X) → (b : X') → ProofOrCE {𝓂 = 𝓂} {𝓃 = 𝓃} (P a b)

matchOrCE : {X : Set 𝓂} {X' : Set 𝓃} → {P : X → X' → Set (𝓂 ⊔ 𝓃)} → SimplifierTag → Binary.Decidable P → MatchOrCE P
matchOrCE tag P a b with P a b
... | yes p = proof p
... | no ¬p = ce ¬p tag a b

pcePointwise : {X : Set 𝓂} {X' : Set 𝓃} {P : X → X' → Set (𝓂 ⊔ 𝓃)} → SimplifierTag → MatchOrCE P → MatchOrCE (Pointwise P)
pcePointwise tag isP? [] [] = proof Pointwise.[]
pcePointwise {X = X} tag isP? [] (y ∷ ys) = ce {X = List X} (λ ()) tag [] ys
pcePointwise {X' = X'} tag isP? (x ∷ xs) [] = ce {X' = List X'} (λ ()) tag xs []
pcePointwise tag isP? (x ∷ xs) (y ∷ ys) with isP? x y
... | ce ¬p tag b a = ce (λ { (x∼y Pointwise.∷ pp) → ¬p x∼y}) tag b a
... | proof p with pcePointwise tag isP? xs ys
...   | ce ¬p tag b a = ce (λ { (x∼y Pointwise.∷ pp) → ¬p pp}) tag b a
...   | proof ps = proof (p Pointwise.∷ ps)

```
