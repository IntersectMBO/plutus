---
title: Algorithmic.Evaluation
layout: page
---
```
module Algorithmic.Evaluation where
```

## Imports

```
open import Data.Nat using (ℕ;zero;suc)
open import Relation.Binary.PropositionalEquality using (refl)
open import Utils using (*;Either;inj₁;RuntimeError;return)
open RuntimeError

open import Type using (∅)
open import Type.BetaNormal using (_⊢Nf⋆_)
open import Algorithmic using (_⊢_;∅)
open _⊢_
open import Algorithmic.ReductionEC using (Value;Error;_—↠_;_—→_;E-error)
open import Algorithmic.ReductionEC.Progress using  (Progress;done;progress;step)
open _—↠_
```

## Evaluation

As previously, gas is specified by a natural number.
```
data Gas : Set where
  gas : ℕ → Gas
```
When our evaluator returns a term `N`, it will either give evidence that
`N` is a value or indicate that it ran out of gas.
```
data Finished {A : ∅ ⊢Nf⋆ *} :  (N : ∅ ⊢ A) →  Set where

   done : ∀ N →
       Value N
       ----------
     → Finished N

   out-of-gas : ∀{N} →
       ----------
       Finished N

   error : {L : ∅ ⊢ A} → Error L → Finished L

   -- is this actually possible?
--   neutral : {L : ∅ ⊢ A} → Neutral L → Finished L
```
Given a term `L` of type `A`, the evaluator will, for some `N`, return
Ma reduction sequence from `L` to `N` and an indication of whether
reduction finished.
```
data Steps : ∀ {A : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Set where

  steps : {A : ∅ ⊢Nf⋆ *} {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L


```

```
eval—→  : ∀{A : ∅ ⊢Nf⋆ *} → {t t' : ∅ ⊢ A} → t —→ t' →
  Steps t' → Steps t
eval—→ p (steps ps q) = steps (trans—↠ p ps) q
```

The evaluator takes gas and a term and returns the corresponding steps.
```
eval : ∀ {A : ∅ ⊢Nf⋆ *} → Gas → (M : ∅ ⊢ A) → Steps M
evalProg : ∀{A : ∅ ⊢Nf⋆ *} → Gas → {t : ∅ ⊢ A} → Progress t → Steps t

eval (gas zero) M = steps refl—↠ out-of-gas
eval (gas (suc n)) M = evalProg (gas n) (progress M)

evalProg g (step {N = .(error _)} (_—→_.ruleErr Algorithmic.ReductionEC.[] refl)) = steps refl—↠ (error E-error)
evalProg g (step {N = t'} p)  = eval—→ p (eval g t')
evalProg g (done VM) = steps refl—↠ (done _ VM)

stepper : {A : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → ℕ → Either RuntimeError (∅ ⊢ A)
stepper {A} t n with eval (gas n) t
... | steps x (done t' v) = return t'
... | steps x out-of-gas  = inj₁ gasError
... | steps x (error _)   = return (error A)

```

