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
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation; convert; reflexive)
open import Relation.Nullary.Product using (_×-dec_)
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
data pureFD : Relation where
  forcedelay : {X : Set} → {x x' : X ⊢} → pureFD x x' → pureFD (force (delay x)) x'
  pushfd : {X : Set} → {x x' : Maybe X ⊢} → {y y' : X ⊢}
         → pureFD x x'
         → pureFD y y'
         → pureFD (force ((ƛ x) · y)) ((ƛ (force x')) · y')
  _⨾_ : {X : Set} → {x x'' x' : X ⊢}
         → pureFD x x''
         → pureFD x'' x'
         → pureFD x x'
  translationfd : {X : Set} → {x x' : X ⊢}
         → Translation pureFD x x'
         → pureFD x x'

  appfd : {X : Set} → {x : Maybe X ⊢} → {y z : X ⊢} → pureFD (((ƛ x) · y) · z) (ƛ (x · (weaken z)) · y)
  appfd⁻¹ : {X : Set} → {x : Maybe X ⊢} → {y z : X ⊢} → pureFD (ƛ (x · (weaken z)) · y) (((ƛ x) · y) · z)

_ : pureFD {Maybe ⊥} (force (delay (` nothing))) (` nothing)
_ = forcedelay (translationfd Translation.var)

forceappdelay : pureFD {Maybe ⊥} (force ((ƛ (delay (` nothing))) · (` nothing))) ((ƛ (` nothing)) · (` nothing))
forceappdelay = (pushfd (translationfd (Translation.delay Translation.var)) (translationfd reflexive)) ⨾ (translationfd (Translation.app (Translation.ƛ (Translation.istranslation
                                                                                                                                                          (forcedelay (translationfd Translation.var)))) Translation.var))

ê : Maybe (Maybe (Maybe (Maybe (Maybe (Maybe (Maybe (Maybe (Maybe (Maybe ⊥)))))))))
ê = just (just (just (just (just (just (just (just (just nothing))))))))

_ : pureFD {Maybe ⊥} (force (force (delay (delay (` nothing))))) (` nothing)
_ = translationfd (Translation.force (Translation.istranslation (forcedelay (translationfd reflexive)))) ⨾ forcedelay (translationfd Translation.var)

_ : pureFD {Maybe ⊥} (force (force (ƛ (ƛ (delay (delay (` nothing))) · (` nothing)) · (` nothing)))) (ƛ (ƛ (` nothing) · (` nothing)) · (` nothing))
_ = (translationfd (Translation.force (Translation.istranslation (pushfd (translationfd reflexive) (translationfd reflexive))))) ⨾ ((translationfd (Translation.force (Translation.app (Translation.ƛ (Translation.istranslation (pushfd (translationfd reflexive) (translationfd reflexive)))) reflexive))) ⨾ ( pushfd (translationfd reflexive) (translationfd reflexive) ⨾ ((translationfd (Translation.app (Translation.ƛ (Translation.istranslation (pushfd (translationfd reflexive) (translationfd reflexive)))) reflexive)) ⨾ (translationfd (Translation.app (Translation.ƛ (Translation.app (Translation.ƛ (Translation.istranslation ((translationfd (Translation.force (Translation.istranslation (forcedelay (translationfd (Translation.delay Translation.var)))))) ⨾ (forcedelay (translationfd Translation.var))))) reflexive)) reflexive)))))

test4 : {X : Set} {N : Maybe (Maybe X) ⊢} {M M' : X ⊢} → pureFD (force (((ƛ (ƛ (delay N))) · M) · M')) (((ƛ (ƛ N)) · M) · M')
test4 = (translationfd (Translation.force (Translation.istranslation appfd))) ⨾ ((pushfd (translationfd reflexive) (translationfd reflexive)) ⨾ ((translationfd (Translation.app (Translation.ƛ (Translation.istranslation (pushfd (translationfd reflexive) (translationfd reflexive)))) reflexive )) ⨾ (translationfd (Translation.app (Translation.ƛ (Translation.app (Translation.ƛ (Translation.istranslation (forcedelay (translationfd reflexive)))) reflexive)) reflexive) ⨾ appfd⁻¹)))

data FD : ℕ → ℕ → Relation where
  forcefd : (n nₐ : ℕ) → {X : Set} → {x x' : X ⊢} → FD (suc n) nₐ x x' → FD n nₐ (force x) x'
  delayfd : (n nₐ : ℕ) → {X : Set} → {x x' : X ⊢} → FD n nₐ x x' → FD (suc n) nₐ (delay x) x'
  lastdelay : (n nₐ : ℕ) → {X : Set} → {x x' : X ⊢} → Translation (FD zero zero) x x' → FD (suc zero) zero (delay x) x'
  multiappliedfd : (n nₐ : ℕ) → {X : Set} → {x y x' y' : X ⊢}
                   → Translation (FD zero zero) y y'
                   → FD n (suc nₐ) (force x) x'
                   → FD n nₐ (force (x · y)) (x' · y')
  multiabstractfd : (n nₐ : ℕ) → {X : Set} → {x x' : Maybe X ⊢}
                    →  FD n nₐ (force x) x'
                    →  FD n (suc nₐ) (force (ƛ x)) (ƛ x')

{-
data FD : Relation
data aFD : ℕ → ℕ → Relation
data fFD : ℕ → Relation

data aFD where
  appfd : (n nₐ : ℕ) → {X : Set} → {x x' y y' : X ⊢} → Translation FD y y' → aFD n (suc nₐ) (force x) x' → aFD n nₐ (force (x · y)) (x' · y')
  absfd :  (n nₐ : ℕ) → {X : Set} → {x x' : (Maybe X) ⊢} → {y y' : X ⊢} → Translation FD y y' → aFD n nₐ (force x) x' → aFD n (suc nₐ) (force (ƛ x)) (ƛ x')
  ffd : (n nₐ : ℕ) → {X : Set} → {x x' : X ⊢} → fFD n x x' → aFD n zero x x'

data fFD where
  forcefd : (n : ℕ) → {X : Set} → {x x' : X ⊢} → fFD (suc n) x x' → fFD n (force x) x'
  delayfd : (n : ℕ) → {X : Set} → {x x' : X ⊢} → fFD n x x' → fFD (suc n) (delay x) x'
  tfd : (n : ℕ) → {X : Set} → {x x' : X ⊢} → Translation (fFD zero) x x' → fFD zero x x'
  afd : (n : ℕ) → {X : Set} → {x x' : X ⊢} → aFD n zero x x' → fFD n x x'

data FD where
  ffd : {X : Set} → {x x' : X ⊢} → fFD zero x x' → FD x x'
-}
_ : FD zero zero {⊥} (force (ƛ (delay error) · error)) (ƛ error · error)
_ = multiappliedfd zero zero Translation.error
     (multiabstractfd zero zero
      (forcefd zero zero (lastdelay zero zero Translation.error)))

_ : FD zero zero {⊥} (force (delay error)) error
_ = forcefd zero zero (lastdelay zero zero Translation.error)

_ : FD zero zero {⊥} (force (force (delay (delay error)))) error
_ = forcefd zero zero
     (forcefd 1 zero
      (delayfd 1 zero (lastdelay zero zero Translation.error)))

_ : FD zero zero {Maybe ⊥} (force (force (ƛ (ƛ (delay (delay (` nothing))) · (` nothing)) · (` nothing)))) (ƛ (ƛ (` nothing) · (` nothing)) · (` nothing))
_ = forcefd zero zero
     (multiappliedfd 1 zero Translation.var
      (multiabstractfd 1 zero
       (multiappliedfd 1 zero Translation.var
        (multiabstractfd 1 zero
         (forcefd 1 zero
          (delayfd 1 zero (lastdelay zero zero Translation.var)))))))

ForceDelay : {X : Set} {{_ : DecEq X}} → (ast : X ⊢) → (ast' : X ⊢) → Set₁
ForceDelay = Translation (FD zero zero)


```

## FD implies pureFD

The two counters in `FD` track the number of forces and applications removed,
to be "consumed" later. Consequently, at any stage we should be able to put
`n` forces and `nₐ` applications back on to the current term and have a valid
`pureFD` relation.

```
variable
  X : Set
  x x' : X ⊢
  n nₐ : ℕ

{-
nFD→FD : {n nₐ : ℕ} → FD n nₐ x x' → FD zero zero x x'
nFD→FD (forcefd zero nₐ p) = {!!}
nFD→FD (forcefd (suc n) nₐ p) = {!!}
nFD→FD (delayfd zero nₐ p) = {!!}
nFD→FD (delayfd (suc n) nₐ p) = {!!}
nFD→FD (lastdelay n nₐ p) = {!!}
nFD→FD (multiappliedfd n nₐ p p₁) = {!!}
nFD→FD (multiabstractfd n nₐ p) = {!!}
-}

forces : ℕ → X ⊢ → X ⊢
forces zero x = x
forces (suc n) x = forces n (force x)

-- What actually gets applied? Does it matter?....
-- The `y` in the FD rules gets handled separately, here it just
-- matters that there is an application that can be paired
-- with a lambda. `error` has the advantage that it is always
-- in scope, even if it is semantically silly.
applications : ℕ → X ⊢ → X ⊢
applications zero x = x
applications (suc n) (force x) = applications n ((force x) · error)
applications (suc n) x = applications n (x · error) -- This isn't really meaningful because it should never happen
                                                                         -- but I can't think how to exclude it?
{-
nFD→FD : {n nₐ : ℕ} → FD n nₐ x x' → FD zero zero (forces n (applications nₐ x)) (applications nₐ x')
nFD→FD {n = zero} {nₐ = zero} p = p
nFD→FD {x = x} {x' = x'} {n = suc n} {nₐ = zero} p =?
nFD→FD {x = (force x)} {x' = x'} {n = zero} {nₐ = suc nₐ} (forcefd .zero .(suc nₐ) p) = ?
nFD→FD {x = .(force (_ · _))} {x' = .(_ · _)} {n = zero} {nₐ = suc nₐ} (multiappliedfd .zero .(suc nₐ) x p) = {!!}
nFD→FD {x = .(force (ƛ _))} {x' = .(ƛ _)} {n = zero} {nₐ = suc nₐ} (multiabstractfd .zero .nₐ p) = {!!}
nFD→FD {x = x} {x' = x'} {n = suc n} {nₐ = suc nₐ} p = {!!}
-}

FD→pureFD : FD zero zero x x' → pureFD x x'

TFD→TpureFD : Translation (FD zero zero) x x' → Translation pureFD x x'
TFD→TpureFD = convert FD→pureFD


forces-translation : {R : Relation} → (n : ℕ) → Translation R x x' → Translation R (forces n x) (forces n x')
forces-translation zero xx' = xx'
forces-translation (suc n) xx' = forces-translation n (Translation.force xx')

apps-translation : {R : Relation} → (n : ℕ) → Translation R x x' → Translation R (applications n x) (applications n x')
apps-translation zero t = t
apps-translation {x = x} {x' = x'} (suc n) t = {!!}

{-# TERMINATING #-}
FD→pureFD {x = .(force (force _))} {x' = x'} (forcefd .zero .zero (forcefd .1 .zero p)) = (translationfd (Translation.force {!!})) ⨾ (FD→pureFD (forcefd zero zero {!!}))
FD→pureFD {x = .(force (delay _))} {x' = x'} (forcefd .zero .zero (delayfd .0 .zero p)) = forcedelay (FD→pureFD p)
FD→pureFD {x = .(force (delay _))} {x' = x'} (forcefd .zero .zero (lastdelay n nₐ p)) = forcedelay (translationfd (TFD→TpureFD p))
FD→pureFD {x = .(force (force (_ · _)))} {x' = .(_ · _)} (forcefd .zero .zero (multiappliedfd .1 .zero p₁ p)) = {!!}
FD→pureFD {x = .(force (_ · _))} {x' = .(_ · _)} (multiappliedfd .zero .zero p₁ (forcefd .zero .1 p)) = {!!}
FD→pureFD {x = .(force ((_ · _) · _))} {x' = .((_ · _) · _)} (multiappliedfd .zero .zero p₁ (multiappliedfd .zero .1 x₁ p)) = {!!}
FD→pureFD {x = (force (ƛ x · y))} {x' = (ƛ x' · y')} (multiappliedfd .zero .zero p₁ (multiabstractfd .zero .0 p)) = (pushfd (translationfd reflexive) (translationfd reflexive)) ⨾ (translationfd (Translation.app (Translation.ƛ (Translation.istranslation (FD→pureFD p))) (TFD→TpureFD p₁)))

{-
FD→pureFD {x = .(force (force (force (force _))))} {x' = x'} (forcefd .zero .zero (forcefd .1 .zero (forcefd .2 .zero (forcefd .3 .zero p)))) = {!!}
FD→pureFD {x = .(force (force (force (delay _))))} {x' = x'} (forcefd .zero .zero (forcefd .1 .zero (forcefd .2 .zero (delayfd .2 .zero p)))) = (translationfd (Translation.force (Translation.force (Translation.istranslation (forcedelay (translationfd reflexive)))))) ⨾ (FD→pureFD (forcefd zero zero (forcefd 1 zero p)))
FD→pureFD {x = .(force (force (delay _)))} {x' = x'} (forcefd .zero .zero (forcefd .1 .zero (delayfd .1 .zero p))) = (translationfd (Translation.force (Translation.istranslation (forcedelay (translationfd reflexive))))) ⨾ FD→pureFD (forcefd zero zero p)
FD→pureFD {x = .(force (force (force (force (_ · _)))))} {x' = .(_ · _)} (forcefd .zero .zero (forcefd .1 .zero (forcefd .2 .zero (multiappliedfd .3 .zero x p)))) = {!!}
FD→pureFD {x = .(force (force (force (_ · _))))} {x' = .(_ · _)} (forcefd .zero .zero (forcefd .1 .zero (multiappliedfd .2 .zero x p))) = {!!}
FD→pureFD {x = .(force (delay _))} {x' = x'} (forcefd .zero .zero (delayfd .0 .zero p)) = forcedelay (FD→pureFD p)
FD→pureFD {x = .(force (delay _))} {x' = x'} (forcefd .zero .zero (lastdelay n nₐ p)) = forcedelay (translationfd (TFD→TpureFD p))
FD→pureFD {x = (force (force (x · y)))} {x' = (x' · y')} (forcefd .zero .zero (multiappliedfd .1 .zero p p₁)) = {!!}
FD→pureFD {x = (force (x · y))} {x' = (x' · y')} (multiappliedfd .zero .zero p p₁) = {!!}
-}


{-
FD→pureFD : FD x x' → pureFD x x'

TFD→TpureFD : Translation FD x x' → Translation pureFD x x'
TFD→TpureFD = convert FD→pureFD

{-# TERMINATING #-}
FD→pureFD {x = (force (force x))} {x' = x'} (ffd (forcefd .zero (forcefd .1 p))) = transfd x' (Translation.istranslation (FD→pureFD (ffd (forcefd zero (forcefd 1 p))))) reflexive
FD→pureFD {x = (force (delay x))} {x' = x'} (ffd (forcefd .zero (delayfd .0 p))) = forcedelay x x'
                                                                                     (Translation.istranslation (FD→pureFD (ffd p)))
FD→pureFD {x = force (force (ƛ x · y))} {x' = ƛ x' · y'} (ffd (forcefd .zero (afd .1 (appfd .1 .zero p₁ p₂)))) = transfd (force (ƛ (force x) · y)) (Translation.force (Translation.istranslation (pushfd reflexive reflexive))) (Translation.istranslation (transfd ( ((force (ƛ (force x))) · y)) (Translation.istranslation {!!}) {!!}))
FD→pureFD {x = force (force ((x · x₁) · y))} {x' = x' · y'} (ffd (forcefd .zero (afd .1 (appfd .1 .zero p₁ p₂)))) = {!!}
FD→pureFD {x = force x} {x' = x'} (ffd (forcefd .zero (afd .1 (ffd .1 nₐ x₁)))) = FD→pureFD (ffd (forcefd zero x₁))
FD→pureFD {x = x} {x' = x'} (ffd (tfd n (Translation.istranslation p))) = FD→pureFD (ffd p)
FD→pureFD {x = x} {x' = x'} (ffd (tfd n p)) = transfd x' (TFD→TpureFD (Translation.istranslation (ffd (tfd n p)))) reflexive
FD→pureFD {x = force ((x · y) · z)} {x' = (x' · y') · z'} (ffd (afd .zero (appfd .zero .zero p (appfd .zero .1 p₁ p₂)))) = {!!}
FD→pureFD {x = force ((ƛ x) · y)} {x' = (ƛ x') · y'} (ffd (afd .zero (appfd .zero .zero p (absfd .zero .0 p₁ p₂)))) = transfd ((ƛ (force x) · y)) (Translation.istranslation (pushfd reflexive reflexive)) (Translation.app (Translation.ƛ (Translation.istranslation (FD→pureFD (ffd (afd zero p₂))))) (TFD→TpureFD p))
FD→pureFD {x = x} {x' = x'} (ffd (afd .zero (ffd .zero nₐ x₁))) = FD→pureFD (ffd x₁)

-}



```
## Decision Procedure


```
{-
isForceDelay? : {X : Set} {{_ : DecEq X}} → Binary.Decidable (Translation (FD zero zero) {X})

{-# TERMINATING #-}
isFD? : {X : Set} {{_ : DecEq X}} → (n nₐ : ℕ) → Binary.Decidable (FD n nₐ {X})

isFD? n nₐ ast ast' with isForce? isTerm? ast

-- If it doesn't start with force then it isn't going to match this translation, unless we have some delays left
isFD? zero nₐ ast ast' | no ¬force = no λ { (forcefd .zero .nₐ x .ast' xx) → ¬force (isforce (isterm x)) ; (multiappliedfd .zero .nₐ x y x' y' x₁ xx) → ¬force (isforce (isterm (x · y))) ; (multiabstractfd .zero nₐ x x' xx) → ¬force (isforce (isterm (ƛ x))) }
isFD? (suc n) nₐ ast ast' | no ¬force with (isDelay? isTerm? ast)
... | no ¬delay = no λ { (forcefd .(suc n) .nₐ x .ast' xx) → ¬force (isforce (isterm x)) ; (delayfd .n .nₐ x .ast' xx) → ¬delay (isdelay (isterm x)) ; (lastdelay n nₐ x .ast' x₁) → ¬delay (isdelay (isterm x)) ; (multiappliedfd .(suc n) .nₐ x y x' y' x₁ xx) → ¬force (isforce (isterm (x · y))) ; (multiabstractfd .(suc n) nₐ x x' xx) → ¬force (isforce (isterm (ƛ x))) }
... | yes (isdelay (isterm t)) with (isForceDelay? t ast') ×-dec (n ≟ zero) ×-dec (nₐ ≟ zero)
... | yes (p , refl , refl) = yes (lastdelay zero zero t ast' p)
... | no ¬zero with isFD? n nₐ t ast'
... | no ¬p = no λ { (delayfd .n .nₐ .t .ast' xxx) → ¬p xxx ; (lastdelay n nₐ .t .ast' x) → ¬zero (x , refl , refl)}
... | yes p = yes (delayfd n nₐ t ast' p)

-- If there is an application we can increment the application counter
isFD? n nₐ ast ast' | yes (isforce (isterm t)) with (isApp? isTerm? isTerm?) t
isFD? n nₐ ast ast' | yes (isforce (isterm t)) | yes (isapp (isterm t₁) (isterm t₂)) with (isApp? isTerm? isTerm?) ast'
isFD? n nₐ ast ast' | yes (isforce (isterm t)) | yes (isapp (isterm t₁) (isterm t₂)) | no ¬isApp = no λ { (multiappliedfd .n .nₐ .t₁ .t₂ x' y' x xx) → ¬isApp (isapp (isterm x') (isterm y')) }
isFD? n nₐ ast ast' | yes (isforce (isterm t)) | yes (isapp (isterm t₁) (isterm t₂)) | yes (isapp (isterm t₁') (isterm t₂')) with (isFD? n (suc nₐ) (force t₁) t₁') ×-dec (isForceDelay? t₂ t₂')
... | yes (pfd , pfd2) = yes (multiappliedfd n nₐ t₁ t₂ t₁' t₂' pfd2 pfd)
... | no ¬FD = no λ { (multiappliedfd .n .nₐ .t₁ .t₂ .t₁' .t₂' x xx) → ¬FD (xx , x) }

-- If there is a lambda we can decrement the application counter unless we have reached zero
isFD? n nₐ ast ast' | yes (isforce (isterm t)) | no ¬isApp with (isLambda? isTerm? t)
isFD? n (suc nₐ ) ast ast' | yes (isforce (isterm t)) | no ¬isApp | yes (islambda (isterm t₂)) with (isLambda? isTerm?) ast'
... | no ¬ƛ = no λ { (multiabstractfd .n .nₐ .t₂ x' xx) → ¬ƛ (islambda (isterm x')) }
... | yes (islambda (isterm t₂')) with (isFD? n nₐ (force t₂) t₂')
... | yes p = yes (multiabstractfd n nₐ t₂ t₂' p)
... | no ¬p = no λ { (multiabstractfd .n .nₐ .t₂ .t₂' xx) → ¬p xx }
-- If we have zero in the application counter then we can't descend further
isFD? n zero ast ast' | yes (isforce (isterm t)) | no ¬isApp | yes (islambda (isterm t₂)) = no λ { (forcefd .n .zero .(ƛ t₂) .ast' ()) }

-- If we have matched none of the patterns then we need to consider nesting.
isFD? n nₐ ast ast' | yes (isforce (isterm t)) | no ¬isApp | no ¬ƛ with isFD? (suc n) nₐ t ast'
... | yes p = yes (forcefd n nₐ t ast' p)
... | no ¬p = no λ { (forcefd .n .nₐ .t .ast' xx) → ¬p xx ; (multiappliedfd .n .nₐ x y x' y' x₁ xx) → ¬isApp (isapp (isterm x) (isterm y)) ; (multiabstractfd .n nₐ x x' xx) → ¬ƛ (islambda (isterm x)) }

isForceDelay? = translation? (isFD? zero zero)
-}
```
