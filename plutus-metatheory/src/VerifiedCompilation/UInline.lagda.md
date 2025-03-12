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
open import VerifiedCompilation.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation; convert; reflexive)
import Relation.Binary as Binary using (Decidable)
open import Untyped.RenamingSubstitution using (_[_])
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Untyped.RenamingSubstitution using (weaken)
open import Data.Empty using (⊥)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

```
## Translation Relation

Abstractly, inlining is much like β-reduction - where a term is applied to a lambda,
the term is substituted in. This can be expressed quite easily and cleanly with the
substitution operation from the general metatheory.

```
data pureInline : Relation where
  tr : {X : Set} {{_ : DecEq X}} {x x' : X ⊢} → Translation pureInline x x' → pureInline x x'
  _⨾_ : {X : Set} {{_ : DecEq X}} {x x' x'' : X ⊢} → pureInline x x' → pureInline x' x'' → pureInline x x''
  inline : {X : Set} {{_ : DecEq X}}{x' : X ⊢} {x : Maybe X ⊢} {y : X ⊢}
         → pureInline (x [ y ]) x'
         → pureInline (ƛ x · y) x'

_ : pureInline {⊥} (ƛ (` nothing) · error) error
_ = inline (tr reflexive)

_ : {X : Set} {a b : X} {{_ : DecEq X}} → pureInline (((ƛ (ƛ ((` (just nothing)) · (` nothing)))) · (` a)) · (` b)) ((` a) · (` b))
_ = tr (Translation.app (Translation.istranslation (inline (tr reflexive))) reflexive) ⨾ inline (tr reflexive)

```
However, this has several intermediate values that are very hard to determine for a decision procedure.

The Haskell code works by building an environment of variable values and then inlines from these. We can
replicate that here to try and make the decision procedure easier.
```
data Env {X : Set}{{_ : DecEq X}} : Set where
  □ : Env
  _,_ : Env {X} → (X ⊢) → Env {X}

```
# Decidable Inline Type

This type is closer to how the Haskell code works, and also closer to the way Jacco's inline example works in the literature.

It recurses to the Translation type, but it needs to not do that initially or the `translation?` decision procedure
will recurse infinitely. Instead there is the `last-sub` constructor to allow the recursion only if at least
something has happened.

```

data Inline {X : Set} {{ _ : DecEq X}} : Env {X} → (X ⊢) → (X ⊢) → Set₁ where
  var : {x y z : X ⊢} {e : Env} → Inline (e , x) z y → Inline e (z · x) y
  last-sub : {x : (Maybe X) ⊢ } {y v : X ⊢} → Translation (Inline □) (x [ v ]) y → Inline (□ , v) (ƛ x) y
  sub : {x : (Maybe X) ⊢ } {y v v₁ : X ⊢} {e : Env} → Inline (e , v₁) (x [ v ]) y → Inline ((e , v₁) , v) (ƛ x) y

_ : {X : Set} {a b : X} {{_ : DecEq X}} → Inline □ (((ƛ (ƛ ((` (just nothing)) · (` nothing)))) · (` a)) · (` b)) ((` a) · (` b))
_ = var (var (sub (last-sub reflexive)))

_ : {X : Set} {a b : X} {{_ : DecEq X}} → Translation (Inline □) (((ƛ (ƛ ((` (just nothing)) · (` nothing)))) · (` a)) · (` b)) ((ƛ ((` (just a)) · (` nothing))) · (` b))

_ = Translation.app (Translation.istranslation (var (last-sub reflexive))) reflexive
```
# Inline implies pureInline
```
--- TODO
postulate
  Inline→pureInline : {X : Set} {{ _ : DecEq X}} → {x y : X ⊢} → Inline □ x y → pureInline x y
```
## Decision Procedure

```
isInline? : {X : Set} {{_ : DecEq X}} → Binary.Decidable (Translation (Inline □))

{-# TERMINATING #-}
isIl? : {X : Set} {{_ : DecEq X}} → (e : Env {X}) → Binary.Decidable (Inline e)
isIl? e ast ast' with (isApp? isTerm? isTerm? ast)
... | yes (isapp (isterm x) (isterm y)) with isIl? (e , y) x ast'
...     | yes p = yes (var p)
...     | no ¬p = no λ { (var p) → ¬p p }
isIl? e ast ast' | no ¬app with (isLambda? isTerm? ast)
isIl? □ ast ast' | no ¬app | no ¬ƛ = no λ { (var p) → ¬app (isapp (isterm _) (isterm _)) }
isIl? (e , v) ast ast' | no ¬app | no ¬ƛ = no λ { (var p) → ¬app (isapp (isterm _) (isterm _)) ; (last-sub t) → ¬ƛ (islambda (isterm _)) ; (sub p) → ¬ƛ (islambda (isterm _)) }
isIl? □ .(ƛ x) ast' | no ¬app | yes (islambda (isterm x)) = no (λ ())
isIl? {X} (□ , v) .(ƛ x) ast' | no ¬app | yes (islambda (isterm x)) with (isInline? (x [ v ]) ast')
... | yes t = yes (last-sub t)
... | no ¬t = no λ { (last-sub t) → ¬t t }
isIl? ((e , v₁) , v) .(ƛ x) ast' | no ¬app | yes (islambda (isterm x)) with (isIl? (e , v₁) (x [ v ]) ast')
... | yes p = yes (sub p)
... | no ¬p = no λ { (sub p) → ¬p p }

isInline? = translation? (isIl? □)

UInline : {X : Set} {{_ : DecEq X}} → (ast : X ⊢) → (ast' : X ⊢) → Set₁
UInline = Translation (Inline □)

```
