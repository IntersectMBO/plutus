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

```
## Translation Relation

Abstractly, inlining is much like β-reduction - where a term is applied to a lambda,
the term is substituted in. This can be expressed quite easily and cleanly with the
substitution operation from the general metatheory.

```
variable
  X : Set
  x x' y : X ⊢

data pureInline : Relation where
  reduce : {{_ : DecEq X}} → Translation pureInline x (ƛ x') → pureInline x x' -- FIXME: ...??
  inline : {{_ : DecEq X}}(x' : Maybe X ⊢) (y y' : X ⊢)
         → Translation pureInline x x'
         → Translation pureInline y y'
         → pureInline (ƛ x · y) (x' [ y' ]) -- FIXME: I'm not sure this is right now...
```
However, this has several intermediate values that are very hard to determine for a decision procedure.

The Haskell code works by building an environment of variable values and then inlines from these. We can
replicate that here to try and make the decision procedure easier.
```
data Env : Set₁ where
  □ : Env
  _,_ : Env → (X ⊢) → Env


variable
  e : Env

data Inline : Env → Relation where
  tr : {{_ : DecEq X}} → Translation (Inline □) {X} x y → Inline □ x y
  var : {{_ : DecEq X}} {z : (Maybe X) ⊢} → Inline (e , x) z (weaken y) → Inline e (ƛ z · x) y
  sub : {{_ : DecEq X}} {x y : X ⊢} → Inline e x y → Inline (e , x) (` nothing) (weaken y)
  sub⁺ : {{_ : DecEq X}} {x y : (Maybe X) ⊢} {v : Maybe X} → Inline e (` v) y → Inline (e , x) (` (just v)) (weaken y)

_ : {X : Set} {a b : X} {{_ : DecEq X}} → pureInline (((ƛ (ƛ ((` (just nothing)) · (` nothing)))) · (` a)) · (` b)) ((` b) · (` a))
_ = {!!}

_ : {X : Set} {a b : X} {{_ : DecEq X}} → Inline □ (((ƛ (ƛ ((` (just nothing)) · (` nothing)))) · (` a)) · (` b)) ((` b) · (` a))
_ = {!!}

```
## Decision Procedure

```
isInline? : {X : Set} {{_ : DecEq X}} → Binary.Decidable (Translation (Inline □) {X})

isIl? : {X : Set} {{_ : DecEq X}} → (e : Env) → Binary.Decidable (Inline e)
isIl? ast ast' = {!!}
{-
isIl? ast ast' with (isApp? (isLambda? isTerm?) isTerm?) ast
... | no ¬p = no λ { (inline x x' y y' x₁ x₂) → ¬p (isapp (islambda (isterm x)) (isterm y)) }
... | yes (isapp (islambda (isterm x)) (isterm y)) = {!!}
-}
isInline? = translation? (isIl? □)

```
