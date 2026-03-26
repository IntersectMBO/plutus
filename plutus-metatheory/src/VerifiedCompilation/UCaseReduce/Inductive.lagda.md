---
title: Equivalence for case-reduce
layout: page
---

## Imports

```
module VerifiedCompilation.UCaseReduce.Inductive where

open import Function using (case_of_)

open import Data.Nat
open import Data.List
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.Maybe
open import Data.Fin
open import Data.Integer using (ℤ ; +_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; subst)

open import Untyped
open import Untyped.CEK using (lookup?)
open import Untyped.Reduction using (iterApp)
open import RawU using (tag2TyTag; tmCon; Tag)
open import Builtin using (Builtin; addInteger)

open import VerifiedCompilation.UntypedTranslation
open import VerifiedCompilation.UntypedViews
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; caseReduceT)
```

## Translation Relation

```
data CaseReduce : Relation where
  casereduce : {X : ℕ} {x : X ⊢} { x' : X ⊢} {vs xs : List (X ⊢)} {i : ℕ}
                         → lookup? i xs ≡ just x
                         → Translation CaseReduce (iterApp x vs) x'
                         → CaseReduce (case (constr i vs) xs) x'
```
## Decision Procedure

```
isCaseReduce? : {X : ℕ} → (ast ast' : X ⊢) → ProofOrCE (Translation CaseReduce {X} ast ast')

justEq : {X : Set} {x x₁ : X} → (just x) ≡ (just x₁) → x ≡ x₁
justEq refl = refl

{-# TERMINATING #-}
isCR? : {X : ℕ} → (ast ast' : X ⊢) → ProofOrCE (CaseReduce ast ast')
isCR? ast ast' with (isCase? (isConstr? allTerms?) allTerms?) ast
... | no ¬p = ce (λ { (casereduce _ _) → ¬p (iscase (isconstr _ (allterms _)) (allterms _))} ) caseReduceT ast ast'
... | yes (iscase (isconstr i (allterms vs)) (allterms xs)) with lookup? i xs in xv
...          | nothing = ce (λ { (casereduce p _) → case trans (sym xv) p of λ { () }} ) caseReduceT ast ast'
...          | just x with isCaseReduce? (iterApp x vs) ast'
...                  | proof p = proof (casereduce xv p)
...                  | ce ¬t t b a = ce (λ { (casereduce p t) → ¬t (subst (λ x → Translation CaseReduce (iterApp x vs) ast') (justEq (trans (sym p) xv)) t)}) t b a

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
_ = casereduce refl reflexive

```
The longer example definately executes in the compiler, but requires some true β-reduction to make work here.
```
ast : 0 ⊢
ast = (case (constr 1 ((con-integer 12) ∷ (con-integer 42) ∷ [])) ( (ƛ (ƛ (` (suc zero)))) ∷ (ƛ (ƛ (case (constr 0 [ (con-integer 99) ]) [ (` zero) ]))) ∷ []) )

ast' : 0 ⊢
ast' = ((con-integer 42) · (con-integer 99))

open import Data.Bool hiding (_≟_)

conInt : ℕ → 0 ⊢
conInt x = con (tmCon (tag2TyTag Tag.integer) (+ x))


does : ∀ {A : Set} → ProofOrCE A → Bool
does (proof _) = true
does (ce _ _ _ _) = false

witness : {A : Set} (d : ProofOrCE A) → does d ≡ true → A
witness (proof P) _ = P
witness (ce _ _ _ _) ()

¬witness : {A : Set} (d : ProofOrCE A) → does d ≡ false → ¬ A
¬witness (proof _) ()
¬witness (ce ¬P _ _ _) _ = ¬P
```

```
module Ex where
  M : 0 ⊢
  M = case (constr 0 []) (constr 0 [] ∷ constr 1 [] ∷ [])

  M' : 0 ⊢
  M' = constr 0 []

  _ : UCaseReduce M M'
  _ = witness (isCaseReduce? M M') refl
```

The UCaseReduce relation does not capture all behaviour of the compiler pass.
Consider for example the following term that reuses `M`.

```
  N : 0 ⊢
  N = case M (constr 42 [] ∷ [])
```

The scrutinee `M` is not a constant, so the `case` expression cannot be
simplified before `M` has been simplified. In other words, the only rule that
applies is the compatibility rule for `case`, but that wouldn't allow us to
relate `N` to the following `N'` which the compiler produces:

```
  N' : 0 ⊢
  N' = constr 42 []

  problem : ¬ UCaseReduce N N'
  problem = ¬witness (isCaseReduce? N N') refl
```

Let's change the `casereduce` rule:

```
data CaseReduce' : Relation where
  casereduce' : {X : ℕ} {x b' : X ⊢} {vs' bs bs' : List (X ⊢)} {i : ℕ}
    → Translation CaseReduce' x (constr i vs')
    → Pointwise (Translation CaseReduce') bs bs'
    → lookup? i bs' ≡ just b'
    → CaseReduce' (case x bs) (iterApp b' vs')
```

It is now unclear how to write a decision procedure, because in order to check
the first premise we need to know `vs'` and `i`. It may seem like `vs'` is
visible from post-term `iterApp b' vs'`, but there are multiple possibilities.
Consider for example the post-term `post`:

```
private
  post : 0 ⊢
  post = builtin addInteger · conInt 2 · conInt 2
```

There are 3 valid options for `vs'` and `b'`, such that `post ≡ iterApp b' vs'`
and we have no direct way to tell which.

Finding `i` is no easier.


```
data CaseReduce'' : Relation where
  casereduce'' : {X : ℕ} {N B M' : X ⊢} {Bs Ns' : List (X ⊢)} {i : ℕ}
    → Translation CaseReduce'' N (constr i Ns')
    → lookup? i Bs ≡ just B
    → Translation CaseReduce'' (iterApp B Ns') M'
    → CaseReduce'' (case N Bs) M'
```

A function that has the same behaviour:

```
{-# TERMINATING #-}
cr'' : ∀ {X} → X ⊢ → X ⊢
cr''* : ∀ {X} → List (X ⊢) → List (X ⊢)
cr'' M@(case N Bs) with cr'' N
... | N'
  with constr? ⋯ ⋯ N'
... | no _ = case (cr'' N) (cr''* Bs)
... | yes (constr! (match! i) (match! Ns'))
  with lookup? i Bs
... | just B = cr'' (iterApp B Ns')
... | nothing = case (cr'' N) (cr''* Bs)
cr'' (` x) = ` x
cr'' (ƛ M) = ƛ (cr'' M)
cr'' (M · N) = (cr'' M) · (cr'' N)
cr'' (force M) = force (cr'' M)
cr'' (delay M) = delay (cr'' M)
cr'' (con x) = con x
cr'' (constr i Ms) = constr i (cr''* Ms)
cr'' (builtin b) = builtin b
cr'' error = error
cr''* [] = []
cr''* (M ∷ Ms) = cr'' M ∷ cr''* Ms

postulate cr-CR'' : ∀ {X} (M : X ⊢) → Translation CaseReduce'' M (cr'' M)
```

Another approach that only normalises discriminees during the decision procedure:

```

-- open import VerifiedCompilation.Compatibility using (pointwise?)
-- 
-- dec-cr : ∀ {X} (M M' : X ⊢) → Dec (CaseReduce'' M M')
-- dec-tr : ∀ {X} (M M' : X ⊢) → Dec (Translation CaseReduce'' M M')
-- 
-- dec-cr M M'
--   with case? ⋯ ⋯ M
-- ... | no ¬case = no (λ {(casereduce'' _ _ _) → ¬case inhabitant})
-- ... | yes (case! (match! N) (match! Bs))
--   with cr'' N in ≡-cr-N
-- ... | N'
--   with constr? ⋯ ⋯ N'
-- ... | no ¬constr = ? -- todo, lemma that if R N (constr i Ns') then cr'' N ≡ constr
-- ... | yes (constr! (match! i) (match! Ns'))
--   with cr-CR'' N
-- ... | H rewrite ≡-cr-N
--   with lookup? i Bs in ≡-lookup
-- ... | nothing = ?
-- ... | just B
--   rewrite ≡-lookup
--   with dec-tr (iterApp B Ns') M'
-- ... | no _ = ?
-- ... | yes CR-iter = yes (casereduce'' H ≡-lookup CR-iter)
-- 
-- dec-tr M M' = {! !}



-- (isCase? (isConstr? allTerms?) allTerms?) ast
-- ... | no ¬p = ce (λ { (casereduce _ _) → ¬p (iscase (isconstr _ (allterms _)) (allterms _))} ) caseReduceT ast ast'
-- ... | yes (iscase (isconstr i (allterms vs)) (allterms xs)) with lookup? i xs in xv
-- ...          | nothing = ce (λ { (casereduce p _) → case trans (sym xv) p of λ { () }} ) caseReduceT ast ast'
-- ...          | just x with isCaseReduce? (iterApp x vs) ast'
-- ...                  | proof p = proof (casereduce xv p)
-- ...                  | ce ¬t t b a = ce (λ { (casereduce p t) → ¬t (subst (λ x → Translation CaseReduce (iterApp x vs) ast') (justEq (trans (sym p) xv)) t)}) t b a

-- isCaseReduce? = translation? caseReduceT isCR?

-- UCaseReduce = Translation CaseReduce
```



