---
title: VerifiedCompilation.UForceDelay
layout: page
---

# Force-Delay Translation Phase
```
module VerifiedCompilation.UForceDelay where

```
## Imports

```
open import VerifiedCompilation.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import VerifiedCompilation.UntypedTranslation using (Translation; TransMatch; translation?; Relation; convert; reflexive)
open import Relation.Nullary using (_×-dec_)
open import Data.Product using (_,_)
import Relation.Binary as Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Data.Empty using (⊥)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Untyped.RenamingSubstitution using (weaken)
open import Data.List using (List; _∷_; [])
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; pcePointwise; MatchOrCE; forceDelayT)

```
## Translation Relation

The Force-Delay translation removes the redundant application of the `force` operator to the `delay` operator.

The simplest case of this is where there is a direct application `force (delay t)` that simply cancels out. However,
the translation also applies to nested or repeated applications, e.g. `force (force (delay (delay t)))`.

Additionally, the translation applies where there is a Lambda abstraction paired with an application, so
`force (ƛ (delay t) · t₂)` for example. There can be multiple abstractions and applications, so long as they
cancel out precisely.

`pureFD` is a mathematical expression of the relation. `FD` is more amenable to building a decision procedure.
Ultimately they should be equivalent.

```

data pureFD {X : Set} {{de : DecEq X}} : X ⊢ → X ⊢ → Set₁ where
  forcedelay : {x x' : X ⊢} → pureFD x x' → pureFD (force (delay x)) x'
  pushfd : {x x' : Maybe X ⊢} → {y y' : X ⊢}
         → pureFD x x'
         → pureFD y y'
         → pureFD (force ((ƛ x) · y)) ((ƛ (force x')) · y')
  _⨾_ : {x x'' x' : X ⊢}
         → pureFD x x''
         → pureFD x'' x'
         → pureFD x x'
  translationfd : {x x' : X ⊢}
         → Translation pureFD x x'
         → pureFD x x'

  appfd : {x : Maybe X ⊢} → {y z : X ⊢} → pureFD (((ƛ x) · y) · z) (ƛ (x · (weaken z)) · y)
  appfd⁻¹ : {x : Maybe X ⊢} → {y z : X ⊢} → pureFD (ƛ (x · (weaken z)) · y) (((ƛ x) · y) · z)

_ : pureFD {Maybe ⊥} (force (delay (` nothing))) (` nothing)
_ = forcedelay (translationfd (Translation.match TransMatch.var))

forceappdelay : pureFD {Maybe ⊥} (force ((ƛ (delay (` nothing))) · (` nothing))) ((ƛ (` nothing)) · (` nothing))
forceappdelay = (pushfd (translationfd (Translation.match
                                         (TransMatch.delay (Translation.match TransMatch.var)))) (translationfd reflexive)) ⨾ (translationfd (Translation.match (TransMatch.app (Translation.match (TransMatch.ƛ (Translation.istranslation
                                                                                                                                                          (forcedelay (translationfd (Translation.match TransMatch.var)))))) (Translation.match TransMatch.var))))

_ : pureFD {Maybe ⊥} (force (force (delay (delay error)))) error
_ = translationfd (Translation.match (TransMatch.force (Translation.istranslation (forcedelay (translationfd reflexive))))) ⨾ forcedelay (translationfd (Translation.match TransMatch.error))

_ : pureFD {Maybe ⊥} (force (force (ƛ (ƛ (delay (delay (` nothing))) · (` nothing)) · (` nothing)))) (ƛ (ƛ (` nothing) · (` nothing)) · (` nothing))
_ = (translationfd (Translation.match (TransMatch.force (Translation.istranslation (pushfd (translationfd reflexive) (translationfd reflexive)))))) ⨾ ((translationfd (Translation.match (TransMatch.force (Translation.match (TransMatch.app (Translation.match (TransMatch.ƛ (Translation.istranslation (pushfd (translationfd reflexive) (translationfd reflexive))))) reflexive))))) ⨾ ( pushfd (translationfd reflexive) (translationfd reflexive) ⨾ ((translationfd (Translation.match (TransMatch.app (Translation.match (TransMatch.ƛ (Translation.istranslation (pushfd (translationfd reflexive) (translationfd reflexive))))) reflexive))) ⨾ (translationfd (Translation.match (TransMatch.app (Translation.match (TransMatch.ƛ (Translation.match (TransMatch.app (Translation.match (TransMatch.ƛ (Translation.istranslation ((translationfd (Translation.match (TransMatch.force (Translation.istranslation (forcedelay (translationfd (Translation.match (TransMatch.delay (Translation.match TransMatch.var))))))))) ⨾ (forcedelay (translationfd (Translation.match TransMatch.var))))))) reflexive)))) reflexive))))))

test4 : {X : Set} {{_ : DecEq X}} {N : Maybe (Maybe X) ⊢} {M M' : X ⊢} → pureFD (force (((ƛ (ƛ (delay N))) · M) · M')) (((ƛ (ƛ N)) · M) · M')
test4 = (translationfd (Translation.match (TransMatch.force (Translation.istranslation appfd)))) ⨾ ((pushfd (translationfd reflexive) (translationfd reflexive)) ⨾ ((translationfd (Translation.match (TransMatch.app (Translation.match (TransMatch.ƛ (Translation.istranslation (pushfd (translationfd reflexive) (translationfd reflexive))))) reflexive ))) ⨾ (translationfd (Translation.match (TransMatch.app (Translation.match (TransMatch.ƛ (Translation.match (TransMatch.app (Translation.match (TransMatch.ƛ (Translation.istranslation (forcedelay (translationfd reflexive))))) reflexive)))) reflexive)) ⨾ appfd⁻¹)))

variable
  X : Set

data Zipper (X : Set) : Set where
  □ : Zipper X
  force : Zipper X → Zipper X
  _·_ : Zipper X → (X ⊢) → Zipper X

zipwk : Zipper X → Zipper (Maybe X)
zipwk □ = □
zipwk (force z) = force (zipwk z)
zipwk (z · x) = zipwk z · (weaken x)

variable
  z : Zipper X
  x x' y y' : X

```
# FD Relation

If this allowed recursion to `Translation` with an empty zipper it would
recurse infinitely in the decision procedure; if it allowed recursion with
a non-empty zipper it would allow you to transit lambdas and applications
without keeping track. Consequently, it only allows you to recurse to
`Translation` if you have done some work, but then got back to an empty
environment.
```

data FD {X : Set} {{_ : DecEq X}} : Zipper X → X ⊢ → X ⊢ → Set₁ where
  force : FD (force z) x x' → FD z (force x) x'
  delay : FD z x x' → FD (force z) (delay x) x'
  app : FD (z · y') x x' → Translation (FD □) y y' → FD z (x · y) (x' · y')
  abs : FD (zipwk z) x x' → FD (z · y) (ƛ x) (ƛ x')
  last-delay : Translation (FD □) x x' → FD (force □) (delay x) x'
  last-abs : Translation (FD □) x x' → FD (□ · y) (ƛ x) (ƛ x')

ForceDelay : {X : Set} {{_ : DecEq X}} → (ast : X ⊢) → (ast' : X ⊢) → Set₁
ForceDelay = Translation (FD □)

```
# Some tests
```

import RawU

postulate
  One Two Three : RawU.TmCon


simpleSuccess : FD {⊥} □ (force (ƛ (delay (con One)) · (con Two))) (ƛ (con One) · (con Two))
simpleSuccess = force
                 (app (abs (last-delay (Translation.match TransMatch.con)))
                  (Translation.match TransMatch.con))

multiApplied : FD {Maybe ⊥} □ (force (force (ƛ (ƛ (delay (delay (` nothing))) · (` nothing)) · (` nothing)))) (ƛ (ƛ (` nothing) · (` nothing)) · (` nothing))
multiApplied = force
     (force
      (app
       (abs
        (app (abs (delay (last-delay (Translation.match TransMatch.var))))
         (Translation.match TransMatch.var)))
       (Translation.match TransMatch.var)))

nested : FD {⊥} □ (force (delay ((ƛ (force (delay ((ƛ (con Two)) · (con Three))))) · (con One)))) ((ƛ ((ƛ (con Two)) · (con Three))) · (con One))
nested = force
          (delay
           (app
            (abs
             (force
              (delay
               (app (last-abs (Translation.match TransMatch.con))
                (Translation.match TransMatch.con)))))
            (Translation.match TransMatch.con)))

forceDelaySimpleBefore : ⊥ ⊢
forceDelaySimpleBefore = (force ((force ((force (delay (ƛ (delay (ƛ (delay (ƛ (` nothing)))))))) · (con One))) · (con Two))) · (con Three)

forceDelaySimpleAfter : ⊥ ⊢
forceDelaySimpleAfter = (((ƛ (ƛ (ƛ (` nothing)))) · (con One)) · (con Two)) · (con Three)

forceDelaySimple : FD □ forceDelaySimpleBefore forceDelaySimpleAfter
forceDelaySimple = app (force (app (force (app (force (delay (abs (delay (abs (delay (last-abs (Translation.match TransMatch.var)))))))) reflexive)) reflexive)) reflexive
```

## FD implies pureFD

The zipper in `FD` tracks the number of forces and applications removed,
to be "consumed" later. Consequently, at any stage we should be able to put
the forces and applications back on to the current term and have a valid
`pureFD` relation.

```

```
## Decision Procedure

```
isForceDelay? : {X : Set} {{_ : DecEq X}} → MatchOrCE (Translation (FD □) {X})

{-# TERMINATING #-}
isFD? : {X : Set} {{_ : DecEq X}} → (z : Zipper X) → MatchOrCE (FD {X} z)
isFD? □ ast ast' with isForce? isTerm? ast
... | yes (isforce (isterm t)) with isFD? (force □) t ast'
...    | proof p = proof (force p)
...    | ce ¬p tag b a = ce (λ { (force x) → ¬p x} ) tag b a
isFD? □ ast ast' | no ¬force with (isApp? isTerm? isTerm? ast) ×-dec (isApp? isTerm? isTerm? ast')
...    | no ¬app = ce (λ { (force x) → ¬force (isforce (isterm _)) ; (app x x₁) → ¬app (isapp (isterm _) (isterm _) , isapp (isterm _) (isterm _))} ) forceDelayT ast ast'
...    | yes (isapp (isterm t) (isterm y) , isapp (isterm t') (isterm y')) with isForceDelay? y y'
...       | ce ¬yt tag b a = ce (λ { (app x x₁) → ¬yt x₁ }) tag b a
...       | proof yt with isFD? (□ · y') t t'
...          | proof p = proof (app p yt)
...          | ce ¬p tag b a = ce (λ { (app x x₁) → ¬p x} ) tag b a

isFD? (force z) ast ast' with isDelay? isTerm? ast
... | yes (isdelay (isterm t)) with isFD? z t ast'
...    | proof p = proof (delay p)
isFD? (force □) (delay t) ast' | yes (isdelay (isterm _)) | ce ¬p tag b a with isForceDelay? t ast'
... | ce ¬pt tag b a = ce (λ { (delay x) → ¬p x ; (last-delay x) → ¬pt x }) forceDelayT (delay t) ast'
... | proof pt = proof (last-delay pt)
isFD? (force (force z)) .(delay _) ast' | yes (isdelay (isterm _)) | ce ¬p tag b a = ce (λ { (delay x) → ¬p x }) tag b a
isFD? (force (z · x)) .(delay _) ast' | yes (isdelay (isterm _)) | ce ¬p tag b a = ce (λ { (delay x) → ¬p x }) tag b a
isFD? (force z) ast ast' | no ¬delay with isForce? isTerm? ast
... | yes (isforce (isterm t)) with isFD? (force (force z)) t ast'
...    | proof p = proof (force p)
...    | ce ¬p tag b a = ce (λ { (force x) → ¬p x} ) tag b a
isFD? (force z) ast ast' | no ¬delay | no ¬force with (isApp? isTerm? isTerm? ast) ×-dec (isApp? isTerm? isTerm? ast')
... | no ¬app = ce ( λ { (force x) → ¬force (isforce (isterm _)) ; (delay x) → ¬delay (isdelay (isterm _)) ; (app x x₁) → ¬app (isapp (isterm _) (isterm _) , isapp (isterm _) (isterm _)) ; (last-delay x) → ¬delay (isdelay (isterm _)) }) forceDelayT ast ast'
... | yes (isapp (isterm t) (isterm y), isapp (isterm t') (isterm y')) with isForceDelay? y y'
...    | ce ¬y tag b a = ce (λ { (app x x₁) → ¬y x₁ }) tag b a
...    | proof py with isFD? ((force z) · y') t t'
...       | proof p = proof (app p py)
...       | ce ¬p tag b a = ce (λ { (app x x₁) → ¬p x} ) tag b a

isFD? (z · _) ast ast' with (isLambda? isTerm? ast) ×-dec (isLambda? isTerm? ast')
... | yes (islambda (isterm t) , islambda (isterm t')) with isFD? (zipwk z) t t'
...    | proof p = proof (abs p)
isFD? (□ · _) (ƛ t) (ƛ t') | yes (islambda (isterm _) , islambda (isterm _)) | ce ¬p tag b a with isForceDelay? t t'
... | proof p = proof (last-abs p)
... | ce ¬pt tag bf af = ce (λ { (abs x) → ¬p x ; (last-abs x) → ¬pt x} ) tag bf af
isFD? (force z · _) .(ƛ _) .(ƛ _) | yes (islambda (isterm _) , islambda (isterm _)) | ce ¬p tag b a = ce (λ { (abs x₁) → ¬p x₁} ) tag b a
isFD? ((z · x) · _) .(ƛ _) .(ƛ _) | yes (islambda (isterm _) , islambda (isterm _)) | ce ¬p tag b a = ce (λ { (abs x₂) → ¬p x₂} ) tag b a
isFD? (z · x) ast ast' | no ¬lambda with isForce? isTerm? ast
... | yes (isforce (isterm t)) with isFD? (force (z · x)) t ast'
...    | proof p = proof (force p)
...    | ce ¬p tag b a = ce (λ { (force x₁) → ¬p x₁} ) tag b a
isFD? (z · x) ast ast' | no ¬lambda | no ¬force with (isApp? isTerm? isTerm? ast) ×-dec (isApp? isTerm? isTerm? ast')
... | no ¬app = ce (λ { (force x₁) → ¬force (isforce (isterm _)) ; (app x₁ x) → ¬app (isapp (isterm _) (isterm _) , isapp (isterm _) (isterm _)); (abs _) → ¬lambda (islambda (isterm _) , islambda (isterm _)) ; (last-abs x) → ¬lambda (islambda (isterm _) , islambda (isterm _))} ) forceDelayT ast ast'
... | yes (isapp (isterm t) (isterm y) , isapp (isterm t') (isterm y')) with isForceDelay? y y'
...   | ce ¬y tag b a = ce (λ { (app x₁ x) → ¬y x}) tag b a
...   | proof py with isFD? ((z · x) · y') t t'
...      | proof p = proof (app p py)
...      | ce ¬p tag b a = ce (λ { (app x₁ x) → ¬p x₁} ) tag b a

isForceDelay? = translation? forceDelayT (isFD? □)


```
