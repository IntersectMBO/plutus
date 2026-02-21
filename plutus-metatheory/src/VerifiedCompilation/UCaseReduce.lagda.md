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
open import Untyped.Equality using (DecEq; _≟_;decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; isVar?; allTerms?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay; isvar)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation; convert; reflexive)
open import Relation.Nullary using (_×-dec_)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error; con-integer)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (trans; sym; subst; cong)
open import Untyped.CEK using (lookup?; lookup?-deterministic)
open import Data.Fin using (Fin; zero; suc)
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
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; caseReduceT)
open import Untyped.Reduction using (iterApp)
```

## Translation Relation

```
data CaseReduce : Relation where
  casereduce : {X : ℕ} {x : X ⊢} {vs xs : List (X ⊢)} {i : ℕ}
                         → lookup? i xs ≡ just x
                         → CaseReduce (case (constr i vs) xs) (iterApp x vs)
```
## Decision Procedure

```
isCaseReduce? : {X : ℕ} → (ast ast' : X ⊢) → ProofOrCE (Translation CaseReduce {X} ast ast')

justEq : {X : Set} {x x₁ : X} → (just x) ≡ (just x₁) → x ≡ x₁
justEq refl = refl

isCR? : {X : ℕ} → (ast ast' : X ⊢) → ProofOrCE (CaseReduce ast ast')
isCR? ast ast' with (isCase? (isConstr? allTerms?) allTerms?) ast
... | no ¬p = ce (λ { (casereduce _) → ¬p (iscase (isconstr _ (allterms _)) (allterms _))} ) caseReduceT ast ast'
... | yes (iscase (isconstr i (allterms vs)) (allterms xs)) with lookup? i xs in xv
...          | nothing = ce (λ { (casereduce p) → case trans (sym xv) p of λ { () }} ) caseReduceT ast ast'
...          | just x with ast' ≟ iterApp x vs
...                  | yes refl = proof (casereduce xv)
...                  | no ast'≠ = ce (λ { (casereduce p) → ast'≠ (sym (cong (λ y → iterApp y vs) (justEq (trans (sym xv) p))))}) caseReduceT ast ast'

isCaseReduce? = translation? caseReduceT isCR?

UCaseReduce = Translation CaseReduce

```
## An Example:

(program 1.1.0
  (case (constr 1 (con integer 12) (con integer 42)) (lam x (lam y x)) (lam x (lam y (case (constr 0 (con integer 99)) y))) )
)

becomes:

(program 1.1.0 [ (con integer 42) (con integer 99) ])

_Compiler version: _
```

```
This simple example applies the rule once, and works
```

ast₁ : 1 ⊢
ast₁ = (case (constr 0 [ (con-integer 99) ]) [ (` zero) ])
ast₁' : 1 ⊢
ast₁' = ((` zero) · (con-integer 99))

_ : CaseReduce ast₁ ast₁'
_ = casereduce refl

```
The longer example definately executes in the compiler, but requires some true β-reduction to make work here.
```
ast : 0 ⊢
ast = (case (constr 1 ((con-integer 12) ∷ (con-integer 42) ∷ [])) ( (ƛ (ƛ (` (suc zero)))) ∷ (ƛ (ƛ (case (constr 0 [ (con-integer 99) ]) [ (` zero) ]))) ∷ []) )

ast' : 0 ⊢
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
open import Untyped.CEK using (stepper; step)
open import Builtin using (Builtin; addInteger; subtractInteger)

ex1 : 0 ⊢
ex1 = (((ƛ (ƛ (((builtin subtractInteger) · (` zero)) · (` (suc zero)))))) · (con-integer 2)) · (con-integer 3) --- \× . \y . x - y ==>  2 - 3

ex2 : 0 ⊢
ex2 = (((ƛ (ƛ (((builtin subtractInteger) · (` (suc zero))) · (` zero))))) · (con-integer 3)) · (con-integer 2) --- \x . \y . y - x ==> 2 - 3

```
