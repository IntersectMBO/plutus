---
title: Certificate
layout: page
---
# Certificates

## Verifying Compiler Transformations Against Translation Relations

Given a list of ASTs and an indication of which pass transforms each AST to the next, the certifier determines whether each transformation satisfies the corresponding translation relation.

If it does, the certifier produces a proof.
Otherwise, it rejects the transformation, either with a refutation showing that the translation relation does not hold, or without one.
We refer to the former as a _decision procedure_, and the latter as a _checking procedure_.

There are several reasons why checking procedures can be desirable, even though they don't produce refutations:

- A decision procedure can be viewed as a checking procedure together with a completeness proof.
  Separating these concerns can improve performance, since the completeness proof is not something users need to run.
- In some cases, deciding whether the translation relation is satisfied can be computationally difficult.
  A checking procedure allows the use of heuristics that may be incomplete (i.e., they may fail to find a proof even when one exists), but are efficient and work well in practice.
- In some cases, it can be easier to conclude that a proof cannot exist than to construct an explicit refutation.
  For example, classic reasoning may establish the nonexistence of a proof, whereas a decision procedure must still construct an explicit refutation, which can be substantially more expensive.
- Checking procedures are often easier to develop and maintain.
  This makes it easier to keep the certifier up to date: when a compiler pass is added or modified, a checking procedure can be implemented or updated quickly and made available to users, while completeness proofs (if desired) can be developed later.

```
module VerifiedCompilation.Certificate where

open import VerifiedCompilation.Trace public
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
open import Data.Bool.Base using (Bool; false; true; not)
open import Function.Base using (_∘_)

variable
  𝓁 𝓂 : Level

data CertResult (P : Set 𝓁) : Set (suc 𝓁) where
  proof : (p : P) → CertResult P
  ce : (¬p : ¬ P) → {X X' : Set} → OptTag → X → X' → CertResult P
  abort : {X X' : Set} → OptTag → X → X' → CertResult P

-- | Result of a decision procedure: either a proof or a counterexample
data ProofOrCE (P : Set 𝓁) : Set (suc 𝓁) where
  proof : (p : P) → ProofOrCE P
  ce : (¬p : ¬ P) → {X X' : Set} → OptTag → X → X' → ProofOrCE P

isProof? : {P : Set 𝓁} → ProofOrCE P → Bool
isProof? (proof _) = true
isProof? (ce _ _ _ _) = false

isCE? : {P : Set 𝓁} → ProofOrCE P → Bool
isCE? = not ∘ isProof?

-- | Result of a checking procedure: either a proof or a failure
data Proof? (P : Set 𝓁) : Set (suc 𝓁) where
  proof : (p : P) → Proof? P
  abort : {X X' : Set} → OptTag → X → X' → Proof? P

infixl 1 _>>=_

_>>=_ : ∀ {𝓁 𝓁′} {P : Set 𝓁} {P′ : Set 𝓁′} → Proof? P → (P → Proof? P′) → Proof? P′
proof p >>= k = k p
abort tag b a >>= _ = abort tag b a

-- Shorthands for deciders/checkers/certifiers

DecidableCE : {X X' : Set} {𝓁 : Level} → (P : X → X' → Set 𝓁) → Set (suc 𝓁)
DecidableCE {X} {X'} P = (a : X) → (b : X') → ProofOrCE (P a b)

Checkable : {X X' : Set} → (P : X → X' → Set) → Set₁
Checkable {X} {X'} P = (a : X) → (b : X') → Proof? (P a b)

Certifiable : {X : Set} (P : X → X → Set) → Set₁
Certifiable {X} P = ∀ (a b : X) → CertResult (P a b)

-- Conversions

checker : ∀ {X} {P : X → X → Set} → Checkable P → Certifiable P
checker f x y with f x y
... | proof p = proof p
... | abort tag a b = abort tag a b

decider : ∀ {X} {P : X → X → Set} → DecidableCE P → Certifiable P
decider f x y with f x y
... | proof p = proof p
... | ce ¬p tag a b = ce ¬p tag a b

decToPCE : {X : Set} {P : Set} → OptTag → Dec P → {before after : X} → ProofOrCE P
decToPCE _ (yes p) = proof p
decToPCE tag (no ¬p) {before} {after} = ce ¬p tag before after

pceToDec : {P : Set} → ProofOrCE P → Dec P
pceToDec (proof p) = yes p
pceToDec (ce ¬p _ _ _) = no ¬p

matchOrCE : {X X' : Set} {𝓁 : Level} → {P : X → X' → Set 𝓁} → OptTag → Binary.Decidable P → DecidableCE P
matchOrCE tag P a b with P a b
... | yes p = proof p
... | no ¬p = ce ¬p tag a b

pcePointwise : {X X' : Set} {𝓁 : Level} {P : X → X' → Set 𝓁} → OptTag → DecidableCE P → DecidableCE (Pointwise P)
pcePointwise tag isP? [] [] = proof Pointwise.[]
pcePointwise {X = X} tag isP? [] (y ∷ ys) = ce (λ ()) {X = List X} tag [] ys
pcePointwise {X' = X'} tag isP? (x ∷ xs) [] = ce (λ ()) {X' = List X'} tag xs []
pcePointwise tag isP? (x ∷ xs) (y ∷ ys) with isP? x y
... | ce ¬p tag b a = ce (λ { (x∼y Pointwise.∷ pp) → ¬p x∼y}) tag b a
... | proof p with pcePointwise tag isP? xs ys
...   | ce ¬p tag b a = ce (λ { (x∼y Pointwise.∷ pp) → ¬p pp}) tag b a
...   | proof ps = proof (p Pointwise.∷ ps)

```
