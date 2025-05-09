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
open import Data.List using (List; []; _∷_)
```
## Translation Relation

Abstractly, inlining is much like β-reduction - where a term is applied to a
lambda, the term is substituted in. However, the UPLC compiler's inliner
sometimes performs "partial" inlining, where some instances of a variable are
inlined and some not. This is straightforward in the Haskell, which retains
variable names, but requires some more complexity to work with de Brujin
indicies and intrinsic scopes.

The Haskell code works by building an environment of variable values and then
inlines from these. We can replicate that here, although we need to track the
applications and the bindings separately to keep them in the right order.
```
variable
  X Y : Set

listWeaken : List (X ⊢) → List ((Maybe X) ⊢)
listWeaken [] = []
listWeaken (v ∷ vs) = ((weaken v) ∷ (listWeaken vs))

data Bind : (X : Set) → Set₁ where
  □ : Bind X
  _,_ : (b : Bind X) → (Maybe X ⊢) → Bind (Maybe X)

bind : Bind X → X ⊢ → Bind (Maybe X)
bind b t = (b , weaken t)

```
Note that `get` weakens the terms as it retrieves them.
```
get : Bind X → X → Maybe (X ⊢)
get □ x = nothing
get (b , v) nothing = just v
get (b , v) (just x) with get b x
... | nothing = nothing
... | just v₁ = just (weaken v₁)

```
# Decidable Inline Type

It recurses to the Translation type, but it needs to not do that initially or
the `translation?` decision procedure will recurse infinitely, so it is
limited to only matching a `Translation` in a non-empty environment.

Translation requires the `Relation` to be defined on an arbitrary,
unconstrained scope, but `Inlined a e` would be constrained by the
scope of the terms in `a` and `e`. Consequently we have to introduce a
new scope `Y`, but will only have constructors for places where this
matches the scope of the environment.
```

data Inlined : List (X ⊢) → Bind X → {Y : Set} {{ _ : DecEq Y}} → (Y ⊢) → (Y ⊢) → Set₁ where
  sub : {{ _ : DecEq X}} {v : X} {e : List (X ⊢)} {b : Bind X} {t : X ⊢}
          → (get b v) ≡ just t
          → Inlined e b (` v) t
  complete : {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X} {t₁ t₂ v : X ⊢}
          → Inlined (v ∷ e) b t₁ t₂
          → Inlined e b (t₁ · v) t₂
  partial : {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X} {t₁ t₂ v : X ⊢}
          → Inlined (v ∷ e) b t₁ t₂
          → Inlined e b (t₁ · v) (t₂ · v)
  ƛ : {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X}  {t₁ t₂ : Maybe X ⊢} {v : X ⊢}
          → Inlined (listWeaken e) (bind b v) t₁ t₂
          → Inlined (v ∷ e) b (ƛ t₁) (ƛ t₂)
  ƛ+ : {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X} {t₁ : Maybe X ⊢} {t₂ v : X ⊢}
          → Inlined (listWeaken e) (bind b v) t₁ (weaken t₂)
          → Inlined (v ∷ e) b (ƛ t₁) t₂
  -- Two forms on "non-empty" environments.
  tran₁ : {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X} {t₁ t₂ v : X ⊢}
          → Translation (Inlined (v ∷ e) b) t₁ t₂
          → Inlined (v ∷ e) b t₁ t₂
  tran₂ : {{ _ : DecEq X}} {e : List ((Maybe X) ⊢)} {b : Bind X} {v : X ⊢} {t₁ t₂ : Maybe X ⊢}
          → Translation (Inlined e (bind b v)) t₁ t₂
          → Inlined e (bind b v) t₁ t₂

Inline : {X : Set} {{ _ : DecEq X}} → (X ⊢) → (X ⊢) → Set₁
Inline = Translation (Inlined {X = ⊥} [] □)

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

ex1 : Inlined {X = Vars} [] □ beforeEx1 afterEx1
ex1 = complete (complete (ƛ+
                           (ƛ+ (tran₂ (match (app (istranslation (sub refl)) (istranslation (sub refl))))))))

```
Partial inlining is allowed, so  `(\a -> f (a 0 1) (a 2)) g` can become  `(\a -> f (g 0 1) (a 2)) g`
```
beforeEx2 : Vars ⊢
beforeEx2 = (ƛ (((` (just f)) · (((` nothing) · (con Zero)) · (con One))) · ((` nothing) · (con Two)) )) · (` g)

afterEx2 : Vars ⊢
afterEx2 = (ƛ (((` (just f)) · (((` (just g)) · (con Zero)) · (con One))) · ((` nothing) · (con Two)) )) · (` g)

ex2 : Inlined {X = Vars} [] □ {Vars} beforeEx2 afterEx2
ex2 = partial (ƛ (partial
                   (tran₂
                    (match
                     (app (match TransMatch.var)
                      (istranslation (partial (partial (sub refl)))))))))

```
## Decision Procedure

```
isInline? : {X : Set} {{_ : DecEq X}} → (ast ast' : X ⊢) → ProofOrCE (Inline ast ast')

{-# TERMINATING #-}
isIl? : {X : Set} {{_ : DecEq X}} → (e : List (X ⊢)) → (b : Bind X) → {Y : Set} {{_ : DecEq Y}} → (ast ast' : Y ⊢) → ProofOrCE (Inlined e b ast ast')
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

isInline? = translation? inlineT (isIl? [] □)

```
