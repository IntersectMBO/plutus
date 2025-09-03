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
open import Untyped.Equality using (DecEq; _≟_; decPointwise)
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
open import Untyped.Purity using (Pure; isPure?)
open import Builtin using (ifThenElse)
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
  x x' y y' b b' : X

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
  ifThenElse :
    Pure x'
    → Pure y'
    → Translation (FD □) b b'
    → FD (force z) x x'
    → FD (force z) y y'
    → FD (force z) ((((force (builtin ifThenElse)) · b) · x) · y) ((((force (builtin ifThenElse)) · b') · x') · y')

ForceDelay : {X : Set} {{_ : DecEq X}} → (ast : X ⊢) → (ast' : X ⊢) → Set₁
ForceDelay = Translation (FD □)

```
# Some tests
```
open import Untyped using (con-integer)

simpleSuccess : FD {⊥} □ (force (ƛ (delay (con-integer 1)) · (con-integer 2))) (ƛ (con-integer 1) · (con-integer 2))
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

nested : FD {⊥} □ (force (delay ((ƛ (force (delay ((ƛ (con-integer 2)) · (con-integer 3))))) · (con-integer 1)))) ((ƛ ((ƛ (con-integer 2)) · (con-integer 3))) · (con-integer 1))
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
forceDelaySimpleBefore = (force ((force ((force (delay (ƛ (delay (ƛ (delay (ƛ (` nothing)))))))) · (con-integer 1))) · (con-integer 2))) · (con-integer 3)

forceDelaySimpleAfter : ⊥ ⊢
forceDelaySimpleAfter = (((ƛ (ƛ (ƛ (` nothing)))) · (con-integer 1)) · (con-integer 2)) · (con-integer 3)

forceDelaySimple : FD □ forceDelaySimpleBefore forceDelaySimpleAfter
forceDelaySimple = app (force (app (force (app (force (delay (abs (delay (abs (delay (last-abs (Translation.match TransMatch.var)))))))) reflexive)) reflexive)) reflexive

lastDelayBreak : ¬ (FD {⊥} □ (force (delay (con-integer 1))) (con-integer 2))
lastDelayBreak = λ { (force (last-delay (Translation.match ()))) }

lastAbsBreak : ¬ (FD {⊥} □ (force (delay ((ƛ (con-integer 1)) · (con-integer 3)))) ((ƛ (con-integer 2)) · (con-integer 3)))
lastAbsBreak = λ { (force (delay (app (last-abs (Translation.istranslation ())) x₁))) ; (force (delay (app (last-abs (Translation.match ())) x₁))) ; (force (last-delay (Translation.istranslation (app (last-abs (Translation.istranslation ())) x₁)))) ; (force (last-delay (Translation.istranslation (app (last-abs (Translation.match ())) x₁)))) ; (force (last-delay (Translation.match (TransMatch.app (Translation.match (TransMatch.ƛ (Translation.istranslation ()))) x₁)))) ; (force (last-delay (Translation.match (TransMatch.app (Translation.match (TransMatch.ƛ (Translation.match ()))) x₁)))) }

```
This `ifThenElse` example is converted from the Haskell constructors in the Haskell test case,
so is written with a prefix style.
```

ast0 : ⊥ ⊢
ast0 = (force (_·_ (_·_ (_·_ (force (builtin ifThenElse)) (con-integer 1)) (delay (con-integer 1))) (delay (con-integer 2))))

ast1 : ⊥ ⊢
ast1 = (_·_ (_·_ (_·_ (force (builtin ifThenElse)) (con-integer 1)) (con-integer 1)) (con-integer 2))

ifThenElseProof : FD □ ast0 ast1
ifThenElseProof = force (ifThenElse Pure.con Pure.con (Translation.match TransMatch.con) (last-delay (Translation.match TransMatch.con)) (last-delay (Translation.match TransMatch.con)))
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

-- Helper function for the recursion search
ForceFDNeverITE : {X : Set} {{_ : DecEq X}} {z : Zipper X} {b b' x x' y' : X ⊢} → ¬ FD (force z · y') ((force (builtin ifThenElse) · b) · x) ((force (builtin ifThenElse) · b') · x')
ForceFDNeverITE (app (app (force ()) x₁) x)

isFD? □ ast ast' with isForce? isTerm? ast
... | yes (isforce (isterm t)) with isFD? (force □) t ast'
...    | proof p = proof (force p)
...    | ce ¬p tag bf af = ce (λ { (force x) → ¬p x} ) tag bf af
isFD? □ ast ast' | no ¬force with (isApp? isTerm? isTerm? ast) ×-dec (isApp? isTerm? isTerm? ast')
... | yes (isapp (isterm t) (isterm v) , isapp (isterm t') (isterm v')) with isFD? (□ · v') t t' | isForceDelay? v v'
...    | proof p | proof ptv = proof (app p ptv)
...    | proof p | ce ¬pv tag bf af = ce (λ { (app x x₁) → ¬pv x₁ } ) tag bf af
...    | ce ¬p tag bf af | _ = ce (λ { (app x x₁) → ¬p x } ) tag bf af
isFD? □ ast ast' | no ¬force | no ¬app = ce (λ { (force x) → ¬force (isforce (isterm _)) ; (app x x₁) → ¬app (isapp (isterm _) (isterm _) , isapp (isterm _) (isterm _))} ) forceDelayT ast ast'
isFD? (force z) ast ast' with (isApp? isTerm? isTerm? ast) ×-dec (isApp? isTerm? isTerm? ast')
... | yes (isapp (isterm t) (isterm y) , isapp (isterm t') (isterm y')) with isFD? ((force z) · y') t t' | isForceDelay? y y'
... | proof pt | proof py = proof (app pt py)
... | proof pt | ce ¬pty tag bf af with isFD? (force z) y y'
...     | ce ¬ppy tag bf af = ce (λ { (app x x₁) → ¬pty x₁ ; (ifThenElse x x₁ x₂ x₃ x₄) → ¬ppy x₄} ) tag bf af
...     | proof py = ce (λ { (app x x₁) → ¬pty x₁ ; (ifThenElse x x₁ x₂ x₃ x₄) → ForceFDNeverITE pt } ) tag bf af
isFD? (force z) ast ast' | yes (isapp (isterm t) (isterm y) , isapp (isterm t') (isterm y')) | ce ¬papp tag₁ bf₁ af₁ | _ with (isApp? (isApp? (isForce? isBuiltin?) isTerm?) isTerm? t) ×-dec (isApp? (isApp? (isForce? isBuiltin?) isTerm?) isTerm? t')
...   | yes (isapp (isapp (isforce (isbuiltin bi)) (isterm b)) (isterm x), isapp (isapp (isforce (isbuiltin bi')) (isterm b')) (isterm x')) with isPure? x' | isPure? y' | isForceDelay? b b' | isFD? (force z) x x' | isFD? (force z) y y'
...      | no ¬purex | _ | _ | _ | _ = ce (λ { (app xx x) → ¬papp xx ; (ifThenElse x x₁ x₂ xx xx₁) → ¬purex x} ) forceDelayT x x'
...      | yes purex | no ¬purey | _ | _ | _ = ce (λ { (app xx x) → ¬papp xx ; (ifThenElse x x₁ x₂ xx xx₁) → ¬purey x₁} ) forceDelayT y y'
...      | yes purex | yes purey | ce ¬ptb tag bf af | _ | _ = ce (λ { (app xx x) → ¬papp xx ; (ifThenElse x x₁ x₂ xx xx₁) → ¬ptb x₂} ) tag bf af
...      | yes purex | yes purey | proof ptb | ce ¬px tag bf af | _ = ce (λ { (app xx x) → ¬papp xx ; (ifThenElse x x₁ x₂ xx xx₁) → ¬px xx} ) tag bf af
...      | yes purex | yes purey | proof ptb | proof px | ce ¬py tag bf af = ce (λ { (app xx x) → ¬papp xx ; (ifThenElse x x₁ x₂ xx xx₁) → ¬py xx₁} ) tag bf af
...      | yes purex | yes purey | proof ptb | proof px | proof py with (bi ≟ bi') ×-dec (bi ≟ ifThenElse)
...      | yes (refl , refl) = proof (ifThenElse purex purey ptb px py)
...      | no ¬bi=ite = ce (λ { (app xx x) → ¬papp xx ; (ifThenElse x x₁ x₂ xx xx₁) → ¬bi=ite (refl , refl)} ) forceDelayT ast ast'

isFD? (force z) ast ast' | yes (isapp (isterm t) (isterm y) , isapp (isterm t') (isterm y'))  | ce ¬papp tag₁ bf₁ af₁ | _ | no ¬ifThenElse = ce (λ { (app x x₁) → ¬papp x ; (ifThenElse x x₁ x₂ x₃ x₄) → ¬ifThenElse
                                                                                                                                                                                                          (isapp (isapp (isforce (isbuiltin ifThenElse)) (isterm _))
                                                                                                                                                                                                           (isterm _)
                                                                                                                                                                                                           ,
                                                                                                                                                                                                           isapp (isapp (isforce (isbuiltin ifThenElse)) (isterm _))
                                                                                                                                                                                                           (isterm _))} ) tag₁ bf₁ af₁
isFD? (force z) ast ast' | no ¬app with isDelay? isTerm? ast
... | yes (isdelay (isterm t)) with isFD? z t ast'
...     | proof p = proof (delay p)
isFD? (force □) ast ast' | no ¬app | yes (isdelay (isterm t)) | ce ¬p tag bf af with isForceDelay? t ast'
... | proof pp = proof (last-delay pp)
... | ce ¬pp tag bf af = ce (λ { (delay x) → ¬p x ; (last-delay x) → ¬pp x} ) tag bf af
isFD? (force (force z)) ast ast' | no ¬app | yes (isdelay (isterm t)) | ce ¬p tag bf af = ce (λ { (delay x) → ¬p x } ) tag bf af
isFD? (force (z · v)) ast ast' | no ¬app | yes (isdelay (isterm t)) | ce ¬p tag bf af = ce (λ { (delay x) → ¬p x } ) tag bf af
isFD? (force z) ast ast' | no ¬app | no ¬delay with isForce? isTerm? ast
... | no ¬force = ce (λ { (force x) → ¬force (isforce (isterm _)) ; (delay x) → ¬delay (isdelay (isterm _)) ; (app x x₁) → ¬app (isapp (isterm _) (isterm _) , isapp (isterm _) (isterm _)) ; (last-delay x) → ¬delay (isdelay (isterm _)) ; (ifThenElse x x₁ x₂ x₃ x₄) → ¬app (isapp (isterm ((force (builtin ifThenElse) · _) · _)) (isterm _) , isapp (isterm ((force (builtin ifThenElse) · _) · _)) (isterm _))} ) forceDelayT ast ast'
... | yes (isforce (isterm t)) with isFD? (force (force z)) t ast'
...     | proof p = proof (force p)
...     | ce ¬p tag bf af = ce (λ { (force x) → ¬p x} ) tag bf af
isFD? (z · x) ast ast' with (isLambda? isTerm? ast) ×-dec (isLambda? isTerm? ast')
... | yes (islambda (isterm t) , islambda (isterm t')) with isFD? (zipwk z) t t'
...     | proof p = proof (abs p)
isFD? (□ · x) ast ast' | yes (islambda (isterm t) , islambda (isterm t')) | ce ¬p tag bf af with isForceDelay? t t'
... | proof p = proof (last-abs p)
... | ce ¬p tag bf af = ce (λ { (abs xx) → ¬p (Translation.istranslation xx) ; (last-abs x) → ¬p x} ) tag bf af
isFD? ((force z) · x) ast ast' | yes (islambda (isterm t) , islambda (isterm t')) | ce ¬p tag bf af = ce (λ { (abs xx) → ¬p xx } ) tag bf af
isFD? ((z · v) · x) ast ast' | yes (islambda (isterm t) , islambda (isterm t')) | ce ¬p tag bf af = ce (λ { (abs xx) → ¬p xx } ) tag bf af
isFD? (z · x) ast ast' | no ¬lambda with isForce? isTerm? ast
... | yes (isforce (isterm t)) with isFD? (force (z · x)) t ast'
...     | proof p = proof (force p)
...     | ce ¬p tag bf af = ce (λ { (force xx) → ¬p xx} ) tag bf af
isFD? (z · x) ast ast' | no ¬lambda | no ¬force with (isApp? isTerm? isTerm? ast) ×-dec (isApp? isTerm? isTerm? ast')
... | no ¬app = ce (λ { (force xx) → ¬force (isforce (isterm _)) ; (app xx x) → ¬app (isapp (isterm _) (isterm _) , isapp (isterm _) (isterm _)) ; (abs xx) → ¬lambda (islambda (isterm _) , islambda (isterm _)) ; (last-abs x) → ¬lambda (islambda (isterm _) , islambda (isterm _))} ) forceDelayT ast ast'
... | yes (isapp (isterm t) (isterm v) , isapp (isterm t') (isterm v')) with isFD? ((z · x) · v') t t' | isForceDelay? v v'
...   | proof p | proof pvt = proof (app p pvt)
...   | proof p | ce ¬pvt tag bf af = ce (λ { (app xx x) → ¬pvt x} ) tag bf af
...   | ce ¬p tag bf af | _ = ce (λ { (app xx x) → ¬p xx} ) tag bf af
{-
isFD? z ast ast' with isForce? isTerm? ast
isFD? z ast ast' | yes (isforce (isterm t)) with ((isApp? (isApp? (isApp? (isForce? isBuiltin?) isTerm?) (isDelay? isTerm?)) (isDelay? isTerm?)) t) ×-dec ((isApp? (isApp? (isApp? (isForce? isBuiltin?) isTerm?) isTerm?) isTerm?) ast')
isFD? □ (force t) ast' | yes (isforce (isterm _)) | yes ((isapp (isapp (isapp (isforce (isbuiltin bi)) (isterm b)) (isdelay (isterm x))) (isdelay (isterm y))) , (isapp (isapp (isapp (isforce (isbuiltin bi')) (isterm b')) (isterm x')) (isterm y'))) with bi ≟ bi' | bi ≟ ifThenElse | isForceDelay? b b' | isForceDelay? x x' | isForceDelay? y y' | isPure? x | isPure? y
... | no ¬bi≡bi' | _ | _ | _ | _ | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (force (lastIfThenElse x x₁ x₂ x₃ x₄)) → ¬bi≡bi' refl ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬bi≡bi' refl} ) forceDelayT (force t) ast'
... | yes refl | no ¬bi≡ifThenElse | _ | _ | _ | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (force (lastIfThenElse x x₁ x₂ x₃ x₄)) → ¬bi≡ifThenElse refl ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬bi≡ifThenElse refl} ) forceDelayT (force t) ast'
... | yes refl | yes refl | ce ¬pb tag bf af | _ | _ | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (force (lastIfThenElse x x₁ x₂ x₃ x₄)) → ¬pb x₂; (ifThenElse x x₁ xx xx₁ xx₂) → ¬pb (Translation.istranslation xx)} ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | ce ¬px tag bf af | _ | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (force (lastIfThenElse x x₁ x₂ x₃ x₄)) → ¬px x₃; (ifThenElse x x₁ xx xx₁ xx₂) → ¬px (Translation.istranslation xx₁)} ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | proof px | ce ¬py tag bf af | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (force (lastIfThenElse x x₁ x₂ x₃ x₄)) → ¬py x₄; (ifThenElse x x₁ xx xx₁ xx₂) → ¬py (Translation.istranslation xx₂)} ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | proof px |  proof py | no ¬purex | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (force (lastIfThenElse x x₁ x₂ x₃ x₄)) → ¬purex x; (ifThenElse x x₁ xx xx₁ xx₂) → ¬purex x} ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | proof px |  proof py | yes purex | no ¬purey = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (force (lastIfThenElse x x₁ x₂ x₃ x₄)) → ¬purey x₁; (ifThenElse x x₁ xx xx₁ xx₂) → ¬purey x₁} ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | proof px |  proof py | yes purex | yes purey = proof (force (lastIfThenElse purex purey pb px py))
isFD? (z · v) (force t) ast' | yes (isforce (isterm _)) | yes ((isapp (isapp (isapp (isforce (isbuiltin bi)) (isterm b)) (isdelay (isterm x))) (isdelay (isterm y))) , (isapp (isapp (isapp (isforce (isbuiltin bi')) (isterm b')) (isterm x')) (isterm y'))) with bi ≟ bi' | bi ≟ ifThenElse | isFD? (z · v) b b' | isFD? (z · v) x x' | isFD? (z · v) y y' | isPure? x | isPure? y
... | no ¬bi≡bi' | _ | _ | _ | _ | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬bi≡bi' refl} ) forceDelayT (force t) ast'
... | yes refl | no ¬bi≡ifThenElse | _ | _ | _ | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬bi≡ifThenElse refl} ) forceDelayT (force t) ast'
... | yes refl | yes refl | ce ¬pb tag bf af | _ | _ | _ | _ = ce (λ {(force (app (app (app (force ()) x₂) x₁) x)) ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬pb xx} ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | ce ¬px tag bf af | _ | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)); (ifThenElse x x₁ xx xx₁ xx₂) → ¬px xx₁ } ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | proof px | ce ¬py tag bf af | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)); (ifThenElse x x₁ xx xx₁ xx₂) → ¬py xx₂} ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | proof px |  proof py | no ¬purex | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬purex x} ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | proof px |  proof py | yes purex | no ¬purey = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬purey x₁} ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | proof px |  proof py | yes purex | yes purey = proof (ifThenElse purex purey pb px py)
isFD? (force z) (force t) ast' | yes (isforce (isterm _)) | yes ((isapp (isapp (isapp (isforce (isbuiltin bi)) (isterm b)) (isdelay (isterm x))) (isdelay (isterm y))) , (isapp (isapp (isapp (isforce (isbuiltin bi')) (isterm b')) (isterm x')) (isterm y'))) with bi ≟ bi' | bi ≟ ifThenElse | isFD? (force z) b b' | isFD? (force z) x x' | isFD? (force z) y y' | isPure? x | isPure? y
... | no ¬bi≡bi' | _ | _ | _ | _ | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬bi≡bi' refl} ) forceDelayT (force t) ast'
... | yes refl | no ¬bi≡ifThenElse | _ | _ | _ | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬bi≡ifThenElse refl} ) forceDelayT (force t) ast'
... | yes refl | yes refl | ce ¬pb tag bf af | _ | _ | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬pb xx} ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | ce ¬px tag bf af | _ | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬px xx₁ } ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | proof px | ce ¬py tag bf af | _ | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)); (ifThenElse x x₁ xx xx₁ xx₂) → ¬py xx₂} ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | proof px |  proof py | no ¬purex | _ = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬purex x} ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | proof px |  proof py | yes purex | no ¬purey = ce (λ { (force (app (app (app (force ()) x₂) x₁) x)) ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬purey x₁} ) forceDelayT (force t) ast'
... | yes refl | yes refl | proof pb | proof px |  proof py | yes purex | yes purey = proof (ifThenElse purex purey pb px py)
isFD? z ast ast' | yes (isforce (isterm t)) | no ¬itepattern with isFD? (force z) t ast'
... | proof p = proof (force p)
... | ce ¬p tag bf af = ce (λ { (force x) → ¬p x ; (ifThenElse x x₁ x₂ x₃ x₄) → ¬itepattern
                                                                                 (isapp
                                                                                  (isapp (isapp (isforce (isbuiltin ifThenElse)) (isterm _))
                                                                                   (isdelay (isterm _)))
                                                                                  (isdelay (isterm _))
                                                                                  ,
                                                                                  isapp
                                                                                  (isapp (isapp (isforce (isbuiltin ifThenElse)) (isterm _))
                                                                                   (isterm _))
                                                                                  (isterm _))} ) tag bf af
isFD? z ast ast' | no ¬force with (isApp? isTerm? isTerm? ast) ×-dec (isApp? isTerm? isTerm? ast')
... | yes (isapp (isterm t) (isterm v) , isapp (isterm t') (isterm v')) with isFD? (z · v') t t' | isForceDelay? v v'
...     | proof p | proof tv = proof (app p tv)
isFD? □ ast ast' | no ¬force | yes papp | proof pp | ce ¬pv tag bf af = ce (λ { (app x x₁) → ¬pv x₁ } ) tag bf af
isFD? (z · v₁) ast ast' | no ¬force | yes papp | proof pp | ce ¬pv tag bf af = ce (λ { (app x x₁) → ¬pv x₁} ) tag bf af
isFD? (force □) .(_ · _) .(_ · _) | no ¬force | yes (isapp (isterm t) (isterm y) , isapp (isterm t') (isterm y')) | proof pp | ce ¬pv tag bf af with isApp? (isApp? isBuiltin? isTerm?) isTerm? t | isApp? (isApp? isBuiltin? isTerm?) isTerm? t'
... | yes (isapp (isapp (isbuiltin bi) (isterm b)) (isterm x)) | yes (isapp (isapp (isbuiltin bi') (isterm b')) (isterm x'))  = {!!}
... | yes pp | no ¬px = {!!}
... | no ¬p | _ = {!!}
isFD? (force (force z)) .(_ · _) .(_ · _) | no ¬force | yes (isapp (isterm _) (isterm _) , isapp (isterm _) (isterm _)) | proof pp | ce ¬pv tag bf af = ce (λ { (app x x₁) → ¬pv x₁} ) tag bf af
isFD? (force (z · x)) .(_ · _) .(_ · _) | no ¬force | yes (isapp (isterm _) (isterm _) , isapp (isterm _) (isterm _)) | proof pp | ce ¬pv tag bf af = ce (λ { (app x x₁) → ¬pv x₁} ) tag bf af
isFD? z ast ast' | no ¬force | yes papp | ce ¬pp tag bf af | _ = ce (λ { (app x x₁) → ¬pp x ; (lastIfThenElse x x₁ x₂ x₃ x₄) → {!!}} ) tag bf af
isFD? □ ast ast' | no ¬force | no ¬app = ce (λ { (force x) → ¬force (isforce (isterm _)) ; (app x x₁) → ¬app (isapp (isterm _) (isterm _) , isapp (isterm _) (isterm _)) ; (ifThenElse x x₁ x₂ x₃ x₄) → ¬force
                                                                                                                                                                                                             (isforce
                                                                                                                                                                                                              (isterm (((force (builtin ifThenElse) · _) · delay _) · delay _)))} ) forceDelayT ast ast'
isFD? (force z) ast ast' | no ¬force | no ¬app with isDelay? isTerm? ast
... | no ¬delay = ce (λ { (force x) → ¬force (isforce (isterm _)) ; (delay x) → ¬delay (isdelay (isterm _)) ; (app x x₁) → ¬app (isapp (isterm _) (isterm _) , isapp (isterm _) (isterm _)) ; (last-delay x) → ¬delay (isdelay (isterm _)) ; (ifThenElse x x₁ x₂ x₃ x₄) → ¬force
                                                                                                                                                                                                                                                                                 (isforce
                                                                                                                                                                                                                                                                                  (isterm (((force (builtin ifThenElse) · _) · delay _) · delay _))) ; (lastIfThenElse x x₁ x₂ x₃ x₄) → ¬app
                                                                                                                                                                                                                                                                                                                                                                                          (isapp (isterm ((force (builtin ifThenElse) · _) · delay _))
                                                                                                                                                                                                                                                                                                                                                                                           (isterm (delay _))
                                                                                                                                                                                                                                                                                                                                                                                           ,
                                                                                                                                                                                                                                                                                                                                                                                           isapp (isterm ((force (builtin ifThenElse) · _) · _))
                                                                                                                                                                                                                                                                                                                                                                                           (isterm _))} ) forceDelayT ast ast'
... | yes (isdelay (isterm t)) with isFD? z t ast'
...    | proof p = proof (delay p)
isFD? (force □) ast ast' | no ¬force | no ¬app | yes (isdelay (isterm t)) | ce ¬p tag bf af with isForceDelay? t ast'
... | proof p = proof (last-delay p)
... | ce ¬p tag bf af = ce (λ { (delay x) → ¬p (Translation.istranslation x) ; (last-delay x) → ¬p x} ) tag bf af
isFD? (force (force z)) ast ast' | no ¬force | no ¬app | yes (isdelay (isterm t)) | ce ¬p tag bf af = ce (λ { (delay x) → ¬p x } ) tag bf af
isFD? (force (z · v)) ast ast' | no ¬force | no ¬app | yes (isdelay (isterm t)) | ce ¬p tag bf af = ce (λ { (delay x) → ¬p x } ) tag bf af
isFD? (z · v) ast ast' | no ¬force | no ¬app with isLambda? isTerm? ast
... | no ¬lambda = ce (λ { (force xx) → ¬force (isforce (isterm _)) ; (app xx x) → ¬app (isapp (isterm _) (isterm _) , isapp (isterm _) (isterm _)) ; (abs xx) → ¬lambda (islambda (isterm _)) ; (last-abs x) → ¬lambda (islambda (isterm _)) ; (ifThenElse x x₁ xx xx₁ xx₂) → ¬force
                                                                                                                                                                                                                                                                                    (isforce
                                                                                                                                                                                                                                                                                     (isterm (((force (builtin ifThenElse) · _) · delay _) · delay _)))} ) forceDelayT ast ast'
... | yes (islambda (isterm t)) with isLambda? isTerm? ast'
...   | no ¬lamda' = ce (λ { (abs x) → ¬lamda' (islambda (isterm _)) ; (last-abs x) → ¬lamda' (islambda (isterm _))} ) forceDelayT ast ast'
isFD? (z · v) ast ast' | no ¬force | no ¬app | yes (islambda (isterm t)) | yes (islambda (isterm t')) with isFD? (zipwk z) t t'
...      | proof p = proof (abs p)
isFD? (□ · v) ast ast' | no ¬force | no ¬app | yes (islambda (isterm t)) | yes (islambda (isterm t')) | ce ¬p tag bf af with isForceDelay? t t'
... | proof p = proof (last-abs p)
... | ce ¬p tag bf af = ce (λ { (abs x) → ¬p (Translation.istranslation x) ; (last-abs x) → ¬p x } ) tag bf af
isFD? ((force z) · v) ast ast' | no ¬force | no ¬app | yes (islambda (isterm t)) | yes (islambda (isterm t')) | ce ¬p tag bf af = ce (λ { (abs x) → ¬p x } ) tag bf af
isFD? ((z · v₁) · v) ast ast' | no ¬force | no ¬app | yes (islambda (isterm t)) | yes (islambda (isterm t')) | ce ¬p tag bf af = ce (λ { (abs x) → ¬p x } ) tag bf af

-}

isForceDelay? = translation? forceDelayT (isFD? □)


```
