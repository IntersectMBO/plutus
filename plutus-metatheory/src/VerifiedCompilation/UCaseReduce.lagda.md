---
title: VerifiedCompilation.UCaseReduce
layout: page
---

# Case-Reduce Translation Phase
```
module VerifiedCompilation.UCaseReduce where

```
## Imports

```
open import VerifiedCompilation.Equality using (DecEq; _≟_;decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; isVar?; allTerms?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay; isvar)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation; convert; reflexive)
open import Relation.Nullary using (_×-dec_)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error; toWellScoped)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (trans; sym; subst)
open import Untyped.CEK using (lookup?; lookup?-deterministic)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; _∷_; []; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
import Relation.Binary as Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_,_)
open import RawU using (tag2TyTag; tmCon)
open import Agda.Builtin.Int using (Int)
open import Data.Empty using (⊥)
open import Function using (case_of_)
```

## Translation Relation

```
iterApp : {X : Set} → X ⊢ → List (X ⊢) → X ⊢
iterApp x [] = x
iterApp x (v ∷ vs) = iterApp (x · v) vs

data CaseReduce : Relation where
  casereduce : {X : Set} {{_ : DecEq X}} {x : X ⊢} { x' : X ⊢} {vs xs : List (X ⊢)} {i : ℕ}
                         → lookup? i xs ≡ just x
                         → Translation CaseReduce (iterApp x vs) x'
                         → CaseReduce (case (constr i vs) xs) x'
```
## Decision Procedure

```
isCaseReduce? : {X : Set} {{_ : DecEq X}} → Binary.Decidable (Translation CaseReduce {X})

justEq : {X : Set} {x x₁ : X} → (just x) ≡ (just x₁) → x ≡ x₁
justEq refl = refl

{-# TERMINATING #-}
isCR? : {X : Set} {{_ : DecEq X}} → Binary.Decidable CaseReduce
isCR? ast ast' with (isCase? (isConstr? allTerms?) allTerms?) ast
... | no ¬p = no λ { (casereduce _ _) → ¬p (iscase (isconstr _ (allterms _)) (allterms _)) }
... | yes (iscase (isconstr i (allterms vs)) (allterms xs)) with lookup? i xs in xv
...          | nothing = no λ { (casereduce p _) → case trans (sym xv) p of λ { () } }
...          | just x with isCaseReduce? (iterApp x vs) ast'
...                  | yes p = yes (casereduce xv p)
...                  | no ¬t = no λ { (casereduce p t) → ¬t (subst (λ x → Translation CaseReduce (iterApp x vs) ast') (justEq (trans (sym p) xv)) t)}

isCaseReduce? = translation? isCR?

```
## An Example:

(program 1.1.0
  (case (constr 1 (con integer 12) (con integer 42)) (lam x (lam y x)) (lam x (lam y (case (constr 0 (con integer 99)) y))) )
)

becomes:

(program 1.1.0 [ (con integer 42) (con integer 99) ])

_Compiler version: _
```

integer : RawU.TyTag
integer = tag2TyTag RawU.integer

con-integer : {X : Set} → ℕ → X ⊢
con-integer n = (con (tmCon integer (Int.pos n)))

```
This simple example applies the rule once, and works
```

ast₁ : (Maybe ⊥) ⊢
ast₁ = (case (constr 0 [ (con-integer 99) ]) [ (` nothing) ])
ast₁' : (Maybe ⊥) ⊢
ast₁' = ((` nothing) · (con-integer 99))

_ : CaseReduce ast₁ ast₁'
_ = casereduce refl reflexive

```
The longer example definately executes in the compiler, but requires some true β-reduction to make work here.
```
ast : ⊥ ⊢
ast = (case (constr 1 ((con-integer 12) ∷ (con-integer 42) ∷ [])) ( (ƛ (ƛ (` (just nothing)))) ∷ (ƛ (ƛ (case (constr 0 [ (con-integer 99) ]) [ (` nothing) ]))) ∷ []) )

ast' : ⊥ ⊢
ast' = ((con-integer 42) · (con-integer 99))

{-
_ : CaseReduce ast ast'
_ = casereduce refl {!!}
-- This would require unpacking the meaning of the lambdas and applications, not just the AST,
-- so is beyond the scope of this translation relation.
-}

```
## Semantic Equivalence

```
open import VerifiedCompilation.SemanticEquivalence using (SemanticallyEquivalent; Equiv; eq)
open import Untyped.CEK using (stepper; step)
open import Builtin using (Builtin; addInteger; subtractInteger)

ex1 : ⊥ ⊢
ex1 = (((ƛ (ƛ (((builtin subtractInteger) · (` nothing)) · (` (just nothing)))))) · (con-integer 2)) · (con-integer 3) --- \× . \y . x - y ==>  2 - 3

ex2 : ⊥ ⊢
ex2 = (((ƛ (ƛ (((builtin subtractInteger) · (` (just nothing))) · (` nothing))))) · (con-integer 3)) · (con-integer 2) --- \x . \y . y - x ==> 2 - 3

_ : Equiv ex1 ex2
_ = eq {!!}

equiv : SemanticallyEquivalent CaseReduce
equiv {x = (case (constr i xs) vs)} {x' = x'} {p = casereduce lookup t} with stepper 10000000 (Untyped.CEK.ε Untyped.CEK.; Untyped.CEK.[] ▻ (case (constr i xs) vs))
... | s = eq {n = 10000000} {!!}
```
