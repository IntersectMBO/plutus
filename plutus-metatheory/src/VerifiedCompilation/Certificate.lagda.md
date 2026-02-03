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
  𝓁 𝓂 : Level

data ProofOrCE (P : Set 𝓁) : Set (suc 𝓁) where
  proof : (p : P) → ProofOrCE P
  ce : (¬p : ¬ P) → {X X' : Set} → SimplifierTag → X → X' → ProofOrCE P
  abort : {X X' : Set} → SimplifierTag → X → X' → ProofOrCE P

decToPCE : {X : Set} {P : Set} → SimplifierTag → Dec P → {before after : X} → ProofOrCE P
decToPCE _ (yes p) = proof p
decToPCE tag (no ¬p) {before} {after} = ce ¬p tag before after

-- pceToDec : {P : Set} → ProofOrCE P → Dec P
-- pceToDec (proof p) = yes p
-- pceToDec (ce ¬p _ _ _) = no ¬p

MatchOrCE : {X X' : Set} {𝓁 : Level} → (P : X → X' → Set 𝓁) → Set (suc 𝓁)
MatchOrCE {X} {X'} P = (a : X) → (b : X') → ProofOrCE (P a b)

matchOrCE : {X X' : Set} {𝓁 : Level} → {P : X → X' → Set 𝓁} → SimplifierTag → Binary.Decidable P → MatchOrCE P
matchOrCE tag P a b with P a b
... | yes p = proof p
... | no ¬p = ce ¬p tag a b

pcePointwise : {X X' : Set} {𝓁 : Level} {P : X → X' → Set 𝓁} → SimplifierTag → MatchOrCE P → MatchOrCE (Pointwise P)
pcePointwise tag isP? [] [] = proof Pointwise.[]
pcePointwise {X = X} tag isP? [] (y ∷ ys) = ce (λ ()) {X = List X} tag [] ys
pcePointwise {X' = X'} tag isP? (x ∷ xs) [] = ce (λ ()) {X' = List X'} tag xs []
pcePointwise tag isP? (x ∷ xs) (y ∷ ys) with isP? x y
... | ce ¬p tag b a = ce (λ { (x∼y Pointwise.∷ pp) → ¬p x∼y}) tag b a
... | abort tag b a = abort tag b a
... | proof p with pcePointwise tag isP? xs ys
...   | ce ¬p tag b a = ce (λ { (x∼y Pointwise.∷ pp) → ¬p pp}) tag b a
...   | abort tag b a = abort tag b a
...   | proof ps = proof (p Pointwise.∷ ps)

```
