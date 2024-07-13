---
title: VerifiedCompilation.UCaseOfCas
layout: page
---
# Untyped Case of Case Translation Phase

```
module VerifiedCompilation.UCaseOfCase where

```
## Imports

```
open import VerifiedCompilation.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation)

import Relation.Binary as Binary using (Decidable)
import Relation.Unary as Unary using (Decidable)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Untyped.CEK using (BApp; fullyAppliedBuiltin; BUILTIN; stepper; State; Stack)
open import Evaluator.Base using (maxsteps)
open import Builtin using (Builtin; ifThenElse)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Nat using (ℕ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; isEquivalence; cong)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Relation.Nullary.Product using (_×-dec_)
open import Data.Product using (_,_)
open import Data.List using (List; _∷_; [])
```
## Translation Relation

This compiler stage only applies to the very specific case where an `IfThenElse` builtin exists in a `case` expression.
It moves the `IfThenElse` outside and creates two `case` expressions with each of the possible lists of cases. 

This will just be an instance of the `Translation` relation once we define the "before" and "after" patterns.

```
data CoC : Relation where
  isCoC : {X : Set} → (b : X ⊢) (tn fn : ℕ)  (tt tt' ft ft' alts alts' : List (X ⊢)) →
             Pointwise CoC alts alts' →
             Pointwise CoC tt tt' →
             Pointwise CoC ft ft' →
             CoC
               (case ((((force (builtin ifThenElse)) · b) · (constr tn tt)) · (constr fn ft)) alts)
               (force ((((force (builtin ifThenElse)) · b) · (delay (case (constr tn tt') alts'))) · (delay (case (constr fn ft') alts'))))

UntypedCaseOfCase : {X : Set} {{_ : DecEq X}} → (ast : X ⊢) → (ast' : X ⊢) → Set₁
UntypedCaseOfCase = Translation CoC

```
## Decision Procedure

Since this compiler phase is just a syntax re-arrangement in a very particular situation, we can
match on that situation in the before and after ASTs and apply the translation rule for this, or
expect anything else to be unaltered.

This translation matches on exactly one, very specific pattern. Using parameterised Views we can
detect that case. We create two "views" for the two patterns - we will tie together the variables in the
later function `isCoC?`.
```

data CoCCase {X : Set} : (X ⊢) → Set where
  isCoCCase : (b : X ⊢) (tn fn : ℕ)  (tt ft alts : List (X ⊢)) → CoCCase (case ((((force (builtin ifThenElse)) · b) · (constr tn tt)) · (constr fn ft)) alts)
isCoCCase? : {X : Set} → Unary.Decidable (CoCCase {X})
isCoCCase? t with (isCase? (isApp? (isApp? (isApp? (isForce? (isBuiltin?)) isTerm?) (isConstr? (allTerms?))) (isConstr? (allTerms?))) (allTerms?)) t
... | yes (iscase (isapp (isapp (isapp (isforce (isbuiltin ite)) (isterm b)) (isconstr tn (allterms tt))) (isconstr fn (allterms ft))) (allterms alts)) with ite ≟ ifThenElse
... | yes refl = yes (isCoCCase b tn fn tt ft alts)
... | no ¬≡b = no λ { (isCoCCase .b .tn .fn .tt .ft .alts) → ¬≡b refl }
isCoCCase? t  | no ¬CoCCase = no λ { (isCoCCase b tn fn alts tt ft) → ¬CoCCase (iscase
                                                                                 (isapp
                                                                                  (isapp (isapp (isforce (isbuiltin ifThenElse)) (isterm b))
                                                                                   (isconstr tn (allterms alts)))
                                                                                  (isconstr fn (allterms tt)))
                                                                                 (allterms ft)) }
                                                                                 
data CoCForce {X : Set} :  (X ⊢) → Set where
  isCoCForce : (b : (X ⊢)) (tn fn : ℕ) (tt' ft' alts' : List (X ⊢)) → CoCForce (force ((((force (builtin ifThenElse)) · b) · (delay (case (constr tn tt') alts'))) · (delay (case (constr fn ft') alts'))))
isCoCForce? : {X : Set} {{ _ : DecEq X }} → Unary.Decidable (CoCForce {X})
isCoCForce? t with (isForce? (isApp? (isApp? (isApp? (isForce? isBuiltin?) isTerm?) (isDelay? (isCase? (isConstr? allTerms?) allTerms?))) (isDelay? (isCase? (isConstr? allTerms?) allTerms?)))) t
... | no ¬CoCForce = no λ { (isCoCForce b tn fn tt' ft' alts') → ¬CoCForce
                                                                  (isforce
                                                                   (isapp
                                                                    (isapp (isapp (isforce (isbuiltin ifThenElse)) (isterm b))
                                                                     (isdelay (iscase (isconstr tn (allterms tt')) (allterms alts'))))
                                                                    (isdelay (iscase (isconstr fn (allterms ft')) (allterms alts')))))}
... | yes (isforce (isapp (isapp (isapp (isforce (isbuiltin ite)) (isterm b)) (isdelay (iscase (isconstr tn (allterms tt')) (allterms alts'))) ) (isdelay (iscase (isconstr fn (allterms ft')) (allterms alts''))))) with ite ≟ ifThenElse ×-dec  alts' ≟ alts''
... | yes (refl , refl) = yes (isCoCForce b tn fn tt' ft' alts')
... | no ¬p = no λ { (isCoCForce .b .tn .fn .tt' .ft' .alts') → ¬p (refl , refl) }

{-# TERMINATING #-}
isCoC? : {X : Set} {{_ : DecEq X}} → Binary.Decidable (CoC {X})
isCoC? ast ast' with (isCoCCase? ast) ×-dec (isCoCForce? ast')
... | no ¬cf = no λ { (isCoC b tn fn tt tt' ft ft' alts alts' x x₁ x₂) → ¬cf
                                                                          (isCoCCase b tn fn tt ft alts , isCoCForce b tn fn tt' ft' alts') }
... | yes (isCoCCase b tn fn tt ft alts , isCoCForce b₁ tn₁ fn₁ tt' ft' alts') with (b ≟ b₁) ×-dec (tn ≟ tn₁) ×-dec (fn ≟ fn₁) ×-dec (decPointwise isCoC? tt tt') ×-dec (decPointwise isCoC? ft ft') ×-dec (decPointwise isCoC? alts alts')
... | yes (refl , refl , refl , ttpw , ftpw , altpw) = yes (isCoC b tn fn tt tt' ft ft' alts alts' altpw ttpw ftpw)
... | no ¬p = no λ { (isCoC .b .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬p (refl , refl , refl , x₁ , x₂ , x) }

```
This must traverse the ASTs applying the constructors from the transition relation, so where
the structure is unchanged we still need to check the sub-components. The general `UntypedTranslation`
module contains the `Translation` datatype, which is parameterised by "before" and "after" predicates.

For this phase, the `CoCCase` and `CoCForce` patterns define the "before" and "after" respectively, so this
just becomes an instance of `Translation` and the decision procedure can be produced using the generalised
`translation?` procedure and the specific `isCoCCase?` and `isCoCForce?`. 

```
isUntypedCaseOfCase : {X : Set} {{_ : DecEq X}} → Binary.Decidable (Translation CoC {X})
isUntypedCaseOfCase {X} ast ast' = translation? {X} isCoC? ast ast'
```

## Semantic Equivalence

We can show that this translation never alters the semantics of the statement. This is shown
in terms of the CEK machine evaluation. Since it is a simple re-arrangement of the syntax, it
isn't a refinement argument - the state before and after the operation is the same type, and is
unaltered buy the syntax re-arrangement.

This does rely on the encoding of the semantics of `IfThenElse` in the CEK module, since we
need to show that the effective list of cases is the same as it would have been without the re-arrangement.

The `stepper` function uses the CEK machine to evaluate a term. Here we call it with a very
large gas budget and begin in an empty context (which assumes the term is closed).

```
-- TODO: Several approaches are possible. 
--semantic_equivalence : ∀ {X set} {ast ast' : ⊥ ⊢}
 --                    → ⊥ ⊢̂ ast ⊳̂ ast'
 -- <Some stuff about whether one runs out of gas -- as long as neither runs out of gas, _then_ they are equivilent> 
 --                    → (stepper maxsteps  (Stack.ϵ ; [] ▻ ast)) ≡ (stepper maxsteps (Stack.ε ; [] ▻ ast'))

-- ∀ {s : ℕ} → stepper s ast ≡ <valid terminate state> ⇔ ∃ { s' : ℕ } [ stepper s' ast' ≡ <same valid terminate state> ] 
```
