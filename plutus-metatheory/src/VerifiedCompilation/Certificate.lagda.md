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

data CertResult (P : Set 𝓁) : Set (suc 𝓁) where
  proof : (p : P) → CertResult P
  ce : (¬p : ¬ P) → {X X' : Set} → SimplifierTag → X → X' → CertResult P
  abort : {X X' : Set} → SimplifierTag → X → X' → CertResult P

-- | Result of a decision procedure: either a proof or a counterexample
data ProofOrCE (P : Set 𝓁) : Set (suc 𝓁) where
  proof : (p : P) → ProofOrCE P
  ce : (¬p : ¬ P) → {X X' : Set} → SimplifierTag → X → X' → ProofOrCE P

-- | Result of a checking procedure: either a proof or a failure
data Proof? (P : Set 𝓁) : Set (suc 𝓁) where
  proof : (p : P) → Proof? P
  abort : {X X' : Set} → SimplifierTag → X → X' → Proof? P


-- Shorthands for deciders/checkers/certifiers

Decider : {X X' : Set} {𝓁 : Level} → (P : X → X' → Set 𝓁) → Set (suc 𝓁)
Decider {X} {X'} P = (a : X) → (b : X') → ProofOrCE (P a b)

Checker : {X X' : Set} → (P : X → X' → Set) → Set₁
Checker {X} {X'} P = (a : X) → (b : X') → Proof? (P a b)

Certifier : {X X' : Set} {𝓁 : Level} → (P : X → X' → Set 𝓁) → Set (suc 𝓁)
Certifier {X} {X'} P = (a : X) → (b : X') → CertResult (P a b)

-- Conversions

runChecker : ∀ {X X'} {P : X → X' → Set} → Checker P → Certifier P
runChecker f x y with f x y
... | proof p = proof p
... | abort tag a b = abort tag a b

runDecider : ∀ {X X'} {P : X → X' → Set} → Decider P → Certifier P
runDecider f x y with f x y
... | proof p = proof p
... | ce ¬p tag a b = ce ¬p tag a b

decToPCE : {X : Set} {P : Set} → SimplifierTag → Dec P → {before after : X} → ProofOrCE P
decToPCE _ (yes p) = proof p
decToPCE tag (no ¬p) {before} {after} = ce ¬p tag before after

pceToDec : {P : Set} → ProofOrCE P → Dec P
pceToDec (proof p) = yes p
pceToDec (ce ¬p _ _ _) = no ¬p

matchOrCE : {X X' : Set} {𝓁 : Level} → {P : X → X' → Set 𝓁} → SimplifierTag → Binary.Decidable P → Decider P
matchOrCE tag P a b with P a b
... | yes p = proof p
... | no ¬p = ce ¬p tag a b

pcePointwise : {X X' : Set} {𝓁 : Level} {P : X → X' → Set 𝓁} → SimplifierTag → Decider P → Decider (Pointwise P)
pcePointwise tag isP? [] [] = proof Pointwise.[]
pcePointwise {X = X} tag isP? [] (y ∷ ys) = ce (λ ()) {X = List X} tag [] ys
pcePointwise {X' = X'} tag isP? (x ∷ xs) [] = ce (λ ()) {X' = List X'} tag xs []
pcePointwise tag isP? (x ∷ xs) (y ∷ ys) with isP? x y
... | ce ¬p tag b a = ce (λ { (x∼y Pointwise.∷ pp) → ¬p x∼y}) tag b a
... | proof p with pcePointwise tag isP? xs ys
...   | ce ¬p tag b a = ce (λ { (x∼y Pointwise.∷ pp) → ¬p pp}) tag b a
...   | proof ps = proof (p Pointwise.∷ ps)

```
