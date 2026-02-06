---
title: VerifiedCompilation.UForceDelay
layout: page
---

# Force-Delay Translation Phase
```
module VerifiedCompilation.UInline where

```
## Imports

```
open import Untyped.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import VerifiedCompilation.UntypedTranslation using (Translation; TransMatch; translation?; Relation; convert; reflexive)
import Relation.Binary as Binary using (Decidable)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)
open import Untyped.RenamingSubstitution using (_[_])
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Untyped.RenamingSubstitution using (weaken)
open import Data.Empty using (⊥)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof)
open import VerifiedCompilation.Trace
```
## Translation Relation

Abstractly, inlining is much like β-reduction - where a term is applied to a lambda,
the term is substituted in. This can be expressed quite easily and cleanly with the
substitution operation from the general metatheory.

```
data pureInline : Relation where
  tr : {X : ℕ} {x x' : X ⊢} → Translation pureInline x x' → pureInline x x'
  _⨾_ : {X : ℕ} {x x' x'' : X ⊢} → pureInline x x' → pureInline x' x'' → pureInline x x''
  inline : {X : ℕ} {x' : X ⊢} {x : suc X ⊢} {y : X ⊢}
         → pureInline (x [ y ]) x'
         → pureInline (ƛ x · y) x'

_ : pureInline {0} (ƛ (` zero) · error) error
_ = inline (tr reflexive)
{-
_ : {X : ℕ} {a b : X} {{_ : DecEq X}} → pureInline (((ƛ (ƛ ((` (just nothing)) · (` nothing)))) · (` a)) · (` b)) ((` a) · (` b))
_ = tr (Translation.app (Translation.istranslation (inline (tr reflexive))) reflexive) ⨾ inline (tr reflexive)
-}
```
However, this has several intermediate values that are very hard to determine for a decision procedure.

The Haskell code works by building an environment of variable values and then inlines from these. We can
replicate that here to try and make the decision procedure easier.
```
data Env {X : ℕ} : Set where
  □ : Env
  _,_ : Env {X} → (X ⊢) → Env {X}

```
# Decidable Inline Type

This type is closer to how the Haskell code works, and also closer to the way Jacco's inline example works in the literature.

It recurses to the Translation type, but it needs to not do that initially or the `translation?` decision procedure
will recurse infinitely. Instead there is the `last-sub` constructor to allow the recursion only if at least
something has happened.

```

data Inline {X : ℕ} : Env {X} → (X ⊢) → (X ⊢) → Set where
  var : {x y z : X ⊢} {e : Env} → Inline (e , x) z y → Inline e (z · x) y
  last-sub : {x : suc X ⊢ } {y v : X ⊢} → Translation (Inline □) (x [ v ]) y → Inline (□ , v) (ƛ x) y
  sub : {x : suc X ⊢ } {y v v₁ : X ⊢} {e : Env} → Inline (e , v₁) (x [ v ]) y → Inline ((e , v₁) , v) (ƛ x) y

_ : {X : ℕ} {a b : Fin X} → Inline □ (((ƛ (ƛ ((` (suc zero)) · (` zero)))) · (` a)) · (` b)) ((` a) · (` b))
_ = var (var (sub (last-sub reflexive)))

{-
_ : {X : ℕ} {a b : X} {{_ : DecEq X}} → Translation (Inline □) (((ƛ (ƛ ((` (just nothing)) · (` nothing)))) · (` a)) · (` b)) ((ƛ ((` (just a)) · (` nothing))) · (` b))
_ = Translation.app (Translation.istranslation (var (last-sub reflexive))) reflexive
-}
```
# Inline implies pureInline
```
--- TODO
postulate
  Inline→pureInline : {X : ℕ} → {x y : X ⊢} → Inline □ x y → pureInline x y
```
## Decision Procedure

```
isInline? : {X : ℕ} → (ast ast' : X ⊢) → ProofOrCE (Translation (Inline □) ast ast')

{-# TERMINATING #-}
isIl? : {X : ℕ} → (e : Env {X}) → (ast ast' : X ⊢) → ProofOrCE (Inline e ast ast')
isIl? e ast ast' with (isApp? isTerm? isTerm? ast)
... | yes (isapp (isterm x) (isterm y)) with isIl? (e , y) x ast'
...     | proof p = proof (var p)
...     | ce ¬p t b a = ce (λ { (var xx) → ¬p xx}) t b a
isIl? e ast ast' | no ¬app with (isLambda? isTerm? ast)
isIl? □ ast ast' | no ¬app | no ¬ƛ = ce (λ { (var xx) → ¬app (isapp (isterm _) (isterm _))}) inlineT ast ast'
isIl? (e , v) ast ast' | no ¬app | no ¬ƛ = ce (λ { (var xx) → ¬app (isapp (isterm _) (isterm _)) ; (last-sub x) → ¬ƛ (islambda (isterm _)) ; (sub xx) → ¬ƛ (islambda (isterm _))}) inlineT ast ast'
isIl? □ .(ƛ x) ast' | no ¬app | yes (islambda (isterm x)) = ce (λ { ()}) inlineT (ƛ x) ast'
isIl? {X} (□ , v) .(ƛ x) ast' | no ¬app | yes (islambda (isterm x)) with (isInline? (x [ v ]) ast')
... | proof t = proof (last-sub t)
... | ce ¬p t b a = ce (λ { (last-sub x) → ¬p x}) t b a
isIl? ((e , v₁) , v) .(ƛ x) ast' | no ¬app | yes (islambda (isterm x)) with (isIl? (e , v₁) (x [ v ]) ast')
... | proof p = proof (sub p)
... | ce ¬p t b a = ce (λ { (sub xx) → ¬p xx}) t b a

isInline? = translation? inlineT (isIl? □)

UInline : {X : ℕ} → (ast : X ⊢) → (ast' : X ⊢) → Set
UInline = Translation (Inline □)

```
