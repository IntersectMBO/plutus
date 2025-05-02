---
title: VerifiedCompilation.UForceDelay
layout: page
---

# Inliner Translation Phase
```
module VerifiedCompilation.UInline where

```
## Imports

```
open import VerifiedCompilation.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import VerifiedCompilation.UntypedTranslation using (Translation; TransMatch; translation?; Relation; convert; reflexive)
import Relation.Binary as Binary using (Decidable)
open import Untyped.RenamingSubstitution using (_[_]; weaken)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Untyped.RenamingSubstitution using (weaken)
open import Data.Empty using (⊥)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; inlineT)
import RawU
```
## Translation Relation

Abstractly, inlining is much like β-reduction - where a term is applied to a
lambda, the term is substituted in. However, the UPLC compiler's inliner
sometimes performs "partial" inlining, where some instances of a variable are
inlined and some not.

Even in the "complete" case, this has several intermediate values that are very
hard to determine for a decision procedure.

The Haskell code works by building an environment of variable values and then
inlines from these. We can replicate that here.
```
variable
  Γ X Y : Set

data Env : Set → Set → Set₁ where
  □ : Env ⊥ X
  _,_ : (e : Env Γ X) → (X ⊢) → Env (Maybe Γ) X

get : Env Γ X → Γ → X ⊢
get (e , x) (just v) = get e v
get (e , x) nothing = x

envWeaken : Env Γ X → Env Γ (Maybe X)
envWeaken □ = □
envWeaken (e , v) = (envWeaken e , weaken v)
```
# Decidable Inline Type

It recurses to the Translation type, but it needs to not do that initially or
the `translation?` decision procedure will recurse infinitely, so it is
limited to only matching a `Translation` in a non-empty environment.

Translation requires the `Relation` to be defined on an arbitrary,
unconstrained scope, but `Inlined e` would be constrained by the
scope of the terms in `e`. Consequently we have to introduce a
new scope `Y`, but will only have constructors for places where this
matches the scope of the environment.
```

data Inlined : Env Γ X → {Y : Set} {{ _ : DecEq Y}} → (Y ⊢) → (Y ⊢) → Set₁ where
  sub : {{ _ : DecEq X}} → {v : X} {e : Env X X} {t : X ⊢} → {(get e v) ≡ t} → Inlined e (` v) t
  complete : {{ _ : DecEq X}} → {v t₂ : X ⊢} {t : (Maybe X) ⊢} {e : Env Γ X} → Inlined e (t [ v ]) t₂ → Inlined e ((ƛ t) · v) t₂
  partial-app : {{ _ : DecEq X}} → {v v' t t₂ : X ⊢} {e : Env Γ X} → Inlined e v v' → Inlined (e , v') t t₂ → Inlined e (t · v) (t₂ · v)
  partial-ƛ : {{ _ : DecEq X}} → {t t₂ : Maybe X ⊢} {e : Env Γ X} → Inlined {X = Maybe X} (envWeaken e) t t₂ → Inlined e (ƛ t) (ƛ t₂)
  translation : {{ _ : DecEq X}} → {e : Env Γ X} {t t₂ v : X ⊢} → Translation (Inlined (e , v)) t t₂ → Inlined (e , v) t t₂

Inline : {X : Set} {{ _ : DecEq X}} → (X ⊢) → (X ⊢) → Set₁
Inline = Translation (Inlined {X = ⊥} □)

```
# Examples

```
postulate
  Vars : Set
  a b f g : Vars
  eqVars : DecEq Vars
  Zero One Two : RawU.TmCon

instance
  EqVars : DecEq Vars
  EqVars = eqVars

```
"Complete" inlining is just substitution in the same way as β-reduction.
```
open import VerifiedCompilation.UntypedTranslation using (match; istranslation; app; ƛ)
beforeEx1 : Vars ⊢
beforeEx1 = (((ƛ (ƛ ((` (just nothing)) · (` nothing)))) · (` a)) · (` b))

afterEx1 : Vars ⊢
afterEx1 = ((` a) · (` b))

ex1 : {X : Set} {a b : X} {{_ : DecEq X}} → Inlined {X = ⊥} □ beforeEx1 afterEx1
ex1 = {!!} -- (translation (match (app (istranslation (complete (translation reflexive))) reflexive))) ⨾ complete (translation reflexive)

```
Partial inlining is allowed, so  `(\a -> f (a 0 1) (a 2)) g` can become  `(\a -> f (g 0 1) (a 2)) g`
```
beforeEx2 : Vars ⊢
beforeEx2 = (ƛ (((` (just f)) · (((` nothing) · (con Zero)) · (con One))) · ((` nothing) · (con Two)) )) · (` g)

afterEx2 : Vars ⊢
afterEx2 = (ƛ (((` (just f)) · (((` (just g)) · (con Zero)) · (con One))) · ((` nothing) · (con Two)) )) · (` g)

ex2 : Inlined {X = ⊥} □ {Vars} beforeEx2 afterEx2
ex2 = {!!} -- partial-app (translation reflexive) (partial-ƛ ?)

```
## Decision Procedure

```
isInline? : {X : Set} {{_ : DecEq X}} → (ast ast' : X ⊢) → ProofOrCE (Inline ast ast')

{-# TERMINATING #-}
isIl? : {X : Set} {{_ : DecEq X}} → (e : Env Γ X) → {Y : Set} {{_ : DecEq Y}} → (ast ast' : Y ⊢) → ProofOrCE (Inlined e ast ast')
isIl? e ast ast' = {!!}
{-
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
-}

isInline? = translation? inlineT (isIl? □)

```
