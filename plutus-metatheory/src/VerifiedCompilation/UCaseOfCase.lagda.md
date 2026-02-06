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
open import Untyped.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation)
open import VerifiedCompilation.Certificate
open import VerifiedCompilation.Trace

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
open import Relation.Nullary using (_×-dec_)
open import Data.Product using (_,_)
open import Data.List using (List; _∷_; [])
```
## Translation Relation

This compiler stage only applies to the very specific case where an `IfThenElse` builtin exists in a `case` expression.
It moves the `IfThenElse` outside and creates two `case` expressions with each of the possible lists of cases.

This will just be an instance of the `Translation` relation once we define the "before" and "after" patterns.

```
data CoC : Relation where
  isCoC : {X : ℕ} (b : X ⊢) (tn fn : ℕ)  (tt tt' ft ft' alts alts' : List (X ⊢)) →
             Pointwise (Translation CoC) alts alts' →
             Pointwise (Translation CoC) tt tt' →
             Pointwise (Translation CoC) ft ft' →
             CoC
               (case ((((force (builtin ifThenElse)) · b) · (constr tn tt)) · (constr fn ft)) alts)
               (force ((((force (builtin ifThenElse)) · b) · (delay (case (constr tn tt') alts'))) · (delay (case (constr fn ft') alts'))))

CaseOfCase : {X : ℕ} (ast : X ⊢) → (ast' : X ⊢) → Set
CaseOfCase = Translation CoC

```
## Decision Procedure

Since this compiler phase is just a syntax re-arrangement in a very particular situation, we can
match on that situation in the before and after ASTs and apply the translation rule for this, or
expect anything else to be unaltered.

This translation matches on exactly one, very specific pattern. Using parameterised Views we can
detect that case. We create two "views" for the two patterns - we will tie together the variables in the
later function `isCoC?`.
```

data CoCCase {X : ℕ} : (X ⊢) → Set where
  isCoCCase : (b : X ⊢) (tn fn : ℕ)  (tt ft alts : List (X ⊢)) → CoCCase (case ((((force (builtin ifThenElse)) · b) · (constr tn tt)) · (constr fn ft)) alts)
isCoCCase? : {X : ℕ} → Unary.Decidable (CoCCase {X})
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

data CoCForce {X : ℕ} :  (X ⊢) → Set where
  isCoCForce : (b : (X ⊢)) (tn fn : ℕ) (tt' ft' alts' : List (X ⊢)) → CoCForce (force ((((force (builtin ifThenElse)) · b) · (delay (case (constr tn tt') alts'))) · (delay (case (constr fn ft') alts'))))
isCoCForce? : {X : ℕ} → Unary.Decidable (CoCForce {X})
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

```
We can now create the final decision procedure. Because the translation can be applied recursively we need
the individual pattern decision `isCoC?` and the overall translation decision `isUntypedCaseOfCase?` to be mutually
recursive, so the `isUntypedCaseOfCase?` type declaration comes first, with the implementation later.

```
isCaseOfCase? : {X : ℕ} (ast ast' : X ⊢) → ProofOrCE (Translation CoC {X} ast ast')

{-# TERMINATING #-}
isCoC? : {X : ℕ}  (ast ast' : X ⊢) → ProofOrCE (CoC {X} ast ast')
isCoC? ast ast' with (isCoCCase? ast) ×-dec (isCoCForce? ast')
... | no ¬cf = ce (λ { (isCoC b tn fn tt tt' ft ft' alts alts' x x₁ x₂) → ¬cf
                                                                           (isCoCCase b tn fn tt ft alts , isCoCForce b tn fn tt' ft' alts') } ) caseOfCaseT ast ast'
... | yes (isCoCCase b tn fn tt ft alts , isCoCForce b₁ tn₁ fn₁ tt' ft' alts') with (b ≟ b₁) ×-dec (tn ≟ tn₁) ×-dec (fn ≟ fn₁)
... | no ¬p = ce (λ { (isCoC .b .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬p (refl , refl , refl)}) caseOfCaseT ast ast'
... | yes (refl , refl , refl) with pcePointwise caseOfCaseT isCaseOfCase? tt tt'
...   | ce ¬p t b a = ce (λ { (isCoC _ .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬p x₁}) t b a
...   | proof tt=tt' with pcePointwise caseOfCaseT isCaseOfCase? ft ft'
...      | ce ¬p t b a = ce (λ { (isCoC _ .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬p x₂}) t b a
...      | proof ft=ft' with pcePointwise caseOfCaseT isCaseOfCase? alts alts'
...        | ce ¬pp t b a = ce (λ { (isCoC _ .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬pp x}) t b a
...        | proof alts=alts' = proof (isCoC b tn fn tt tt' ft ft' alts alts' alts=alts' tt=tt' ft=ft')

isCaseOfCase? {X} = translation? {X} caseOfCaseT isCoC?

certCaseOfCase : Certifier (CaseOfCase {0})
certCaseOfCase = runDecider isCaseOfCase?
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
