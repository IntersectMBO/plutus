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
open import VerifiedCompilation.UntypedTranslation using (translation?)

open import Relation.Unary as Unary using (Decidable)
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

This translation relation has a constructor for the specific case, and then inductive constructors for everything else
to traverse the ASTs.

```
data CaseOfCase {X : Set} : (X ⊢) → (X ⊢) → Set where
   caseofcase : ∀ (b : X ⊢) (tn fn : ℕ) (alts alts' tt ft tt' ft' : List (X ⊢))
                → Pointwise CaseOfCase alts alts' -- recursive translation for the other case patterns 
                → Pointwise CaseOfCase tt tt' -- recursive translation for the true branch 
                → Pointwise CaseOfCase ft ft' -- recursive translation for the false branch
                ----------------------
                → CaseOfCase
                       (case ((((force (builtin ifThenElse)) · b) · (constr tn tt)) · (constr fn ft)) alts)
                       (force ((((force (builtin ifThenElse)) · b) · (delay (case (constr tn tt') alts'))) · (delay (case (constr fn ft') alts'))))

```

## Decision Procedure

Since this compiler phase is just a syntax re-arrangement in a very particular situation, we can
match on that situation in the before and after ASTs and apply the translation rule for this, or
expect anything else to be unaltered.

This translation matches on exactly one, very specific pattern. Using parameterised Views we can
detect that case.
```
data CoCCase {X : Set} : (X ⊢) → Set where
  isCoCCase : (b : X ⊢) (tn fn : ℕ)  (tt ft alts : List (X ⊢)) → CoCCase (case ((((force (builtin ifThenElse)) · b) · (constr tn tt)) · (constr fn ft)) alts)
isCoCCase? : {X : Set} → Decidable (CoCCase {X})
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
isCoCForce? : {X : Set} {{ _ : DecEq X }} → Decidable (CoCForce {X})
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
This must traverse the ASTs applying the constructors from the transition relation, so where
the structure is unchanged we still need to check the sub-components.

```
{-# TERMINATING #-}
isCaseOfCase? : {X : Set} {{_ : DecEq X}} → (ast : X ⊢) → (ast' : X ⊢) → Dec (CaseOfCase {X} ast ast')
isCaseOfCase? ast ast' with translation? isCoCCase? isCoCForce? ast ast'
... | yes (VerifiedCompilation.UntypedTranslation.istranslation .ast .ast' (isCoCCase b tn fn tt ft alts) (isCoCForce b₁ tn₁ fn₁ tt' ft' alts')) with (b ≟ b₁) ×-dec (tn ≟ tn₁) ×-dec (fn ≟ fn₁) ×-dec (decPointwise isCaseOfCase? alts alts') ×-dec (decPointwise isCaseOfCase? tt tt') ×-dec (decPointwise isCaseOfCase? ft ft') 
...          | yes (refl , refl , refl , pw₁ , pw₂ , pw₃) = yes (caseofcase b tn fn alts alts' tt ft tt' ft' pw₁ pw₂ pw₃)
...          | no ¬b≟b₁ = no λ { (caseofcase .b .tn .fn .alts .alts' .tt .ft .tt' .ft' x x₁ x₂) → ¬b≟b₁ (refl , refl , refl , x , x₁ , x₂) }
isCaseOfCase? .(` _) .(` _) | yes VerifiedCompilation.UntypedTranslation.var = no (λ ())
isCaseOfCase? .(ƛ _) .(ƛ _) | yes (VerifiedCompilation.UntypedTranslation.ƛ xxx) = no (λ ())
isCaseOfCase? .(_ · _) .(_ · _) | yes (VerifiedCompilation.UntypedTranslation.app xxx xxx₁) = no (λ ())
isCaseOfCase? .(force _) .(force _) | yes (VerifiedCompilation.UntypedTranslation.force xxx) = no (λ ())
isCaseOfCase? .(delay _) .(delay _) | yes (VerifiedCompilation.UntypedTranslation.delay xxx) = no (λ ())
isCaseOfCase? .(con _) .(con _) | yes VerifiedCompilation.UntypedTranslation.con = no (λ ())
isCaseOfCase? .(constr _ _) .(constr _ _) | yes (VerifiedCompilation.UntypedTranslation.constr x) = no (λ ())
isCaseOfCase? .(case _ _) .(case _ _) | yes (VerifiedCompilation.UntypedTranslation.case x xxx) = no (λ ())
isCaseOfCase? .(builtin _) .(builtin _) | yes VerifiedCompilation.UntypedTranslation.builtin = no (λ ())
isCaseOfCase? .error .error | yes VerifiedCompilation.UntypedTranslation.error = no (λ ())
isCaseOfCase? ast ast' | no ¬p = no λ { (caseofcase b tn fn alts alts' tt ft tt' ft' x x₁ x₂) → ¬p
                                                                                      (VerifiedCompilation.UntypedTranslation.istranslation
                                                                                       (case
                                                                                        (((force (builtin ifThenElse) · b) · constr tn tt) · constr fn ft)
                                                                                        alts)
                                                                                       (force
                                                                                        (((force (builtin ifThenElse) · b) ·
                                                                                          delay (case (constr tn tt') alts'))
                                                                                         · delay (case (constr fn ft') alts')))
                                                                                       (isCoCCase b tn fn tt ft alts) (isCoCForce b tn fn tt' ft' alts')) }

```
First, handle all the cases where both sides of the translation are the same structure. Only the Case of Case
pattern should change the structure.
```
{-
_⊢̂_⊳̂?_ (` x) (` y) with x ≟ y
...                         | yes refl = yes var
...                         | no ¬p = no (λ { (var) → ¬p refl })
_⊢̂_⊳̂?_ (ƛ ast) (ƛ ast') with _⊢̂_⊳̂?_ ast ast'
...                                  | yes p = yes (ƛ p)
...                                  | no ¬p = no (λ { (ƛ x) → ¬p x })
_⊢̂_⊳̂?_ (ast · ast₁) (ast' · ast'₁) with _⊢̂_⊳̂?_ ast ast' | _⊢̂_⊳̂?_ ast₁ ast'₁
...                                              | yes p1                 | yes p2 = yes (app p1 p2)
...                                              | yes p1                 | no ¬p2 = no λ { (app a a₁) → ¬p2 a₁ }
...                                              | no ¬p1                 | _         = no λ { (app a a₁) → ¬p1 a }
_⊢̂_⊳̂?_ (force ast) (force ast') with _⊢̂_⊳̂?_ ast ast' 
...                                  | yes p = yes (force p)
...                                  | no ¬p = no λ { (force a) → ¬p a }
_⊢̂_⊳̂?_ (delay ast) (delay ast') with _⊢̂_⊳̂?_ ast ast'
...                                  | yes p = yes (delay p)
...                                  | no ¬p = no λ { (delay a) → ¬p a}
_⊢̂_⊳̂?_ (con tm) (con tm') with tm ≟ tm'
...                                  | yes refl = yes con
...                                  | no ¬p = no λ { (con) → ¬p refl }
_⊢̂_⊳̂?_ (constr i ast) (constr i' ast') with i ≟ i' | decPointwise _⊢̂_⊳̂?_ ast ast'
...                                                       | no ¬i≟i  | _       = no λ { (constr pw) → ¬i≟i refl }
...                                                       | yes refl | no ¬p = no λ { (constr pw) → ¬p pw }
...                                                       | yes refl | yes p = yes (constr p)
_⊢̂_⊳̂?_ (case p ast) (case p' ast') with _⊢̂_⊳̂?_ p p' | decPointwise _⊢̂_⊳̂?_ ast ast'
...                                                       | no ¬p⊳p'  | _       = no λ { (case pp pw) → ¬p⊳p' pw }
...                                                       | _             | no ¬p = no λ { (case pp pw) → ¬p pp }
...                                                       | yes p⊳p'   | yes pw = yes (case pw p⊳p')
_⊢̂_⊳̂?_ (builtin b) (builtin b') with b ≟ b'
...                                          | no ¬b=b = no λ { (builtin) → ¬b=b refl }
...                                          | yes refl = yes builtin
_⊢̂_⊳̂?_ error error = yes error
-}
```
If we have `case` translated to `force` we need to be sure that it matches exactly the Case of Case pattern
```
{-
_⊢̂_⊳̂?_ ast ast' with isCoCCase? ast ×-dec isCoCForce? ast'
... | no ¬CoC  = no {!!}
... | yes (isCoCCase b tn fn tt ft alts , isCoCForce b' tn' fn' tt' ft' alts') with b ≟ b' | tn ≟ tn' | fn ≟ fn'  | decPointwise _⊢̂_⊳̂?_ alts alts' | decPointwise _⊢̂_⊳̂?_ tt tt' | decPointwise _⊢̂_⊳̂?_ ft ft'
...         | no ¬b≟b' | _            | _            | _                | _              | _              = no λ { (caseofcase _ _ _ _ _ _ _ _ ) → ¬b≟b' refl } 
...         | yes refl   | no tn≠tn' | _            | _                | _              | _              = no λ { (caseofcase _ _ _ _ _ _ _ _ ) →  tn≠tn' refl } 
...         | yes refl   | yes refl   | no fn≠fn' | _                | _              | _              = no  λ { (caseofcase _ _ _ _ _ _ _ _ ) → fn≠fn' refl }
...         | yes refl   | yes refl   | yes refl   | no ¬pw-alts | _              | _              = no λ { (caseofcase _ _ _ _ _ x _ _ ) → ¬pw-alts x }
...         | yes refl   | yes refl   | yes refl   | yes pw-alts | no tt≠tt'     | _              = no λ { (caseofcase _ _ _ _ _ _ x _ ) → tt≠tt' x }
...         | yes refl   | yes refl   | yes refl   | yes pw-alts | yes ps-tt   | no ft≠ft'     = no λ { (caseofcase _ _ _ _ _ _ _ x) → ft≠ft' x }
...         | yes refl   | yes refl   | yes refl   | yes pw-alts | yes pw-tt  | yes pw-ft   = yes (caseofcase b tn fn fn fn pw-alts pw-tt pw-ft)
-}

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
