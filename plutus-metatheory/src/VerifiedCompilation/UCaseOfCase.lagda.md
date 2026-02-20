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
open import VerifiedCompilation.UntypedViews -- using (Pred; isCase?; isApp?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; pcePointwise; caseOfCaseT)

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
open import RawU using (TmCon)
```

## Translation Relation

This compiler stage only applies to the very specific case where an `IfThenElse` builtin exists in a `case` expression.
It moves the `IfThenElse` outside and creates two `case` expressions with each of the possible lists of cases.


### Case-of-If

This behaviour transforms a `case` that has a saturated `ifThenElse` as discriminee. The pattern of the pre-term:

```
data CaseIfPre {X : ℕ} : (X ⊢) → Set where
  isCaseIfPre :
    {b : X ⊢} {tn fn : ℕ}  {tt ft alts : List (X ⊢)}
    → -------------------------------
    CaseIfPre
      (
        case
          (
            force (builtin ifThenElse)
            · b
            · constr tn tt
            · constr fn ft
          )
          alts
      )
```

And the pattern we expect after:

```
data CaseIfPost {X : ℕ} : (X ⊢) → Set where
  isCaseIfPost :
    (b : (X ⊢)) (tn fn : ℕ) (tt' ft' alts' : List (X ⊢))
    → --------------------------------------------------
    CaseIfPost
      (force
        (
          force (builtin ifThenElse)
          · b
          · delay (case (constr tn tt') alts')
          · delay (case (constr fn ft') alts')
        )
      )
```

### Case-of-Case

```
variable
  X : ℕ
  i j : ℕ  -- indices of constr
  i' j' : ℕ  -- indices of constr

variable
  M : X ⊢
  Ms Ns Ts : List (X ⊢)
  M' : X ⊢
  Ms' Ns' Ts' Ts'' : List (X ⊢)
  K : TmCon

postulate All : ∀ {A : Set} →(A → Set) → List A → Set
```

Constructors and constants are directly scrutinizable:

```

data Scrutinizable : X ⊢ → Set where
  scrut-constr :
    Scrutinizable (constr i Ms)

  -- TODO
  -- scrut-con :
  --   Scrutinizable (con {X} K)
```

A pre-term has a case-of-case, where the inner case's branches are scrunizable.

```
data CaseCasePre : X ⊢ → Set where

  isCaseCasePre :
    All Scrutinizable Ms
    → ------------------
    CaseCasePre
      ( case
          (case M Ms)
            Ns
      )
```

A post-term is simply a single case, so we don't define a separate inductive.

### Translation Relation

The translation relation has two cases that match the compiler's behaviour.

```

data CaseIf (R : X ⊢ → X ⊢ → Set) : X ⊢ → X ⊢ → Set where
  caseIf :
    -- Pointwise R Ms Ms' →
    -- Pointwise R Ns Ns' →
    -- Pointwise R Ts Ts'
    R M M'
    → ------------------
    CaseIf R
      (case
         (
           force (builtin ifThenElse)
           · M
           · constr i Ms
           · constr j Ns
         )
         Ts
      )
      (force
        (
           force (builtin ifThenElse)
           · M' -- TODO, should this be M or M'?
           · delay (case (constr i' Ms') Ts')
           · delay (case (constr j' Ns') Ts'') -- TODO, TS'' should also be TS'? Or pointwise?
        )
      )

open import Data.Sum
open import Data.Unit.Base using (⊤)

-- attempt 1: termination checker fails
-- CaseCase : X ⊢ → X ⊢ → Set
-- CaseCase M M' =
--   CaseIf CaseCase M M' ⊎ ⊤

data CaseCase : X ⊢ → X ⊢ → Set where
    caseIf' : CaseIf CaseCase M M' → CaseCase M M'

caseIf? : (∀ {X} (N N' : X ⊢) → Dec (CaseCase N N') ) → (M M' : X ⊢) → Dec (CaseIf CaseCase M M')
caseIf? caseCase? M M' with
  (case?
    (
      (isForce? (builtin? (_≟_ ifThenElse)))
      ·? ⋯
      ·? (constr? ⋯)
      ·? (constr? ⋯)
    )
    ⋯) M
... | no ¬PM = no λ {(caseIf _) → {! !}} -- todo, write a function f : term → Set that computes the "view"-type of a term and then a general function inhabits : t -> (f t) (maybe it goes both ways?)
... | yes (iscase (isapp (isapp (isapp (isforce (isbuiltin .ifThenElse refl)) (wildcard MB)) (isconstr _ (wildcard _))) (isconstr _ (wildcard _))) (wildcard _)) with
  (force?
    (
      force? (builtin? (_≟_ ifThenElse))
      ·? ⋯
      ·? delay? (case? (constr? ⋯) ⋯)
      ·? delay? (case? (constr? ⋯) ⋯)
    )
  ) M'
... | no _ = {! !}
... | yes (isforce (isapp (isapp (isapp (isforce (isbuiltin .ifThenElse refl)) (wildcard MB')) (isdelay (iscase (isconstr _ (wildcard _)) (wildcard _))) ) (isdelay (iscase (isconstr _ (wildcard _)) (wildcard _)))))
  with caseCase? MB MB'
... | no _ = {! !}
... | yes PMB = yes (caseIf PMB)

caseCase? : (M M' : X ⊢) → Dec (CaseCase M M')
caseCase? M M' with caseIf? caseCase? M M'
... | yes P = yes (caseIf' P)
... | no ¬P = no λ { (caseIf' P) → ¬P P }

data CoC : Relation where
  isCoC : {X : ℕ} (b : X ⊢) (tn fn : ℕ)  (tt tt' ft ft' alts alts' : List (X ⊢)) →
             Pointwise (Translation CoC) alts alts' →
             Pointwise (Translation CoC) tt tt' →
             Pointwise (Translation CoC) ft ft' →
             CoC
               (case
                  (
                    force (builtin ifThenElse)
                    · b
                    · constr tn tt
                    · constr fn ft
                  )
                  alts
               )
               (force
                 (
                    force (builtin ifThenElse)
                    · b
                    · delay (case (constr tn tt') alts')
                    · delay (case (constr fn ft') alts')
                 )
               )

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
isCaseIfPre? : {X : ℕ} → Unary.Decidable (CaseIfPre {X})
isCaseIfPre? t with
  (case?
    (
      (isForce? (builtin? (_≟_ ifThenElse)))
      ·? ⋯
      ·? (constr? ⋯)
      ·? (constr? ⋯)
    )
    ⋯)
    t
... | yes (iscase (isapp (isapp (isapp (isforce (isbuiltin .ifThenElse refl)) (wildcard _)) (isconstr _ (wildcard _))) (isconstr _ (wildcard _))) (wildcard _))
    = yes isCaseIfPre
... | no ¬CaseIfPre
    = no λ { isCaseIfPre →
                ¬CaseIfPre
                  (iscase
                    (isapp
                     (isapp (isapp (isforce (isbuiltin ifThenElse refl)) (wildcard _))
                      (isconstr _ (wildcard _)))
                     (isconstr _ (wildcard _)))
                    (wildcard _)) }


isCaseIfPost? : {X : ℕ} → Unary.Decidable (CaseIfPost {X})
isCaseIfPost? t with
  (force?
    (
      force? (builtin? (_≟_ ifThenElse))
      ·? ⋯
      ·? delay? (case? (constr? ⋯) ⋯)
      ·? delay? (case? (constr? ⋯) ⋯)
    )
  )
  t
... | no ¬CaseIfPost = no λ { (isCaseIfPost b tn fn tt' ft' alts') →
                              ¬CaseIfPost
                                (isforce
                                 (isapp
                                  (isapp (isapp (isforce (isbuiltin ifThenElse refl)) (wildcard b))
                                   (isdelay (iscase (isconstr tn (wildcard tt')) (wildcard alts'))))
                                  (isdelay (iscase (isconstr fn (wildcard ft')) (wildcard alts')))))}
... | yes (isforce (isapp (isapp (isapp (isforce (isbuiltin .ifThenElse refl)) (wildcard b)) (isdelay (iscase (isconstr tn (wildcard tt')) (wildcard alts'))) ) (isdelay (iscase (isconstr fn (wildcard ft')) (wildcard alts''))))) with alts' ≟ alts''
... | yes refl = yes (isCaseIfPost b tn fn tt' ft' alts')
... | no ¬p = no λ { (isCaseIfPost .b .tn .fn .tt' .ft' .alts') → ¬p refl }

```
We can now create the final decision procedure. Because the translation can be applied recursively we need
the individual pattern decision `isCoC?` and the overall translation decision `isUntypedCaseOfCase?` to be mutually
recursive, so the `isUntypedCaseOfCase?` type declaration comes first, with the implementation later.

```

isCaseOfCase? : {X : ℕ} (ast ast' : X ⊢) → ProofOrCE (Translation CoC {X} ast ast')

{-# TERMINATING #-}
isCoC? : {X : ℕ}  (ast ast' : X ⊢) → ProofOrCE (CoC {X} ast ast')
isCoC? ast ast' with (isCaseIfPre? ast) ×-dec (isCaseIfPost? ast')
... | no ¬cf = ce (λ { (isCoC b tn fn tt tt' ft ft' alts alts' x x₁ x₂) → ¬cf
                                                                           (isCaseIfPre , isCaseIfPost b tn fn tt' ft' alts') } ) caseOfCaseT ast ast'
... | yes (isCaseIfPre {b} {tn} {fn} {tt} {ft} {alts} , isCaseIfPost b₁ tn₁ fn₁ tt' ft' alts') with (b ≟ b₁) ×-dec (tn ≟ tn₁) ×-dec (fn ≟ fn₁)
... | no ¬p = ce (λ { (isCoC .b .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬p (refl , refl , refl)}) caseOfCaseT ast ast'
... | yes (refl , refl , refl) with pcePointwise caseOfCaseT isCaseOfCase? tt tt'
...   | ce ¬p t b a = ce (λ { (isCoC _ .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬p x₁}) t b a
...   | proof tt=tt' with pcePointwise caseOfCaseT isCaseOfCase? ft ft'
...      | ce ¬p t b a = ce (λ { (isCoC _ .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬p x₂}) t b a
...      | proof ft=ft' with pcePointwise caseOfCaseT isCaseOfCase? alts alts'
...        | ce ¬pp t b a = ce (λ { (isCoC _ .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬pp x}) t b a
...        | proof alts=alts' = proof (isCoC b tn fn tt tt' ft ft' alts alts' alts=alts' tt=tt' ft=ft')

isCaseOfCase? {X} = translation? {X} caseOfCaseT isCoC?
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
