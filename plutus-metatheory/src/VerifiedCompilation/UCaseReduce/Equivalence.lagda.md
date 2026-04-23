---
title: Equivalence for case-reduce
layout: page
---


## Equivalence relation, normalising on both sides

This version is an experiment to normalise both pre- and post-term, resulting in
a larger relation that can relate more equivalent terms. For example, it can
relate terms where the optimiser did not case-reduce a candidate.

It is also less of a specification of the pass, because it allows the opposite
of reduction, by being symmetric.

## Imports

```
module VerifiedCompilation.UCaseReduce.Equivalence where


open import Function using (case_of_; _$_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.List
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe
open import Data.Fin using (Fin)
open import Relation.Nullary using (Dec; yes; no; ¬_ )
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning

open import Untyped
open import Untyped.Relation.Binary
open import Untyped.Transform
open import Untyped.Equality
open import Untyped.Reduction using (iterApp)
open import Untyped.CEK using (lookup?)

open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; caseReduceT)
open import VerifiedCompilation.UntypedViews
open import VerifiedCompilation.UntypedTranslation using (Translation; TransMatch)

private variable
  X : ℕ
  L M N M' N' : X ⊢
  Ns Ms Ms' Ns' : List (X ⊢)
  i : ℕ
```


## Rewrite rule

```
reduce : ∀ {X} → X ⊢ → X ⊢
reduce M@(case (constr i Ns) Ms) =
  case lookup? i Ms of λ where
    (just N) → iterApp N Ns
    nothing → M
{-# CATCHALL #-}
reduce M = M

norm : ∀ {X} → X ⊢ → X ⊢
norm M = reduce ↑ M

norm* : ∀ {X} → List (X ⊢) → List (X ⊢)
norm* Ns = reduce ↑* Ns
```

## Relation

The relation states that both terms are (syntactically) equal after
normalising with `norm`.

```
CaseReduce : Relation
CaseReduce M N = norm M ≡ norm N
```

## Decision procedure

The decision procedure is straightforward:

```
decide : ∀ {X} (M M' : X ⊢) → ProofOrCE (CaseReduce M M')
decide M M' with norm M ≟ norm M'
... | yes P = proof P
... | no ¬P = ce ¬P caseReduceT M M'
```

## Inductively defined equivalence

Equivalence relation that captures the case-reduce rules:

```
infix 3 _~_

data _~_ {X : ℕ} : X ⊢ → X ⊢ → Set where

  case-constr : ∀ {i : ℕ} →
     lookup? i Ns ≡ just N →
     -----------------------
     case (constr i Ms) Ns ~ iterApp N Ms

  ~-refl :
    ----------
    M ~ M

  ~-trans :
    L ~ M →
    M ~ N →
    -----
    L ~ N

  ~-sym :
    M ~ N →
    -----
    N ~ M

  ~-var : ∀ {x : Fin X} →
    ---------
    ` x ~ ` x

  ~-lam :
    M ~ M' →
    -----------
    ƛ M ~ ƛ M'

  ~-app :
    M ~ M' →
    N ~ N' →
    -----------------
    M · N ~ M' · N'

  ~-force :
    M ~ M' →
    ------------
    force M ~ force M'

  ~-delay :
    M ~ M' →
    ------------
    delay M ~ delay M'

  ~-constr :
    Pointwise _~_ Ms Ms' →
    --------------------
    constr i Ms ~ constr i Ms'

  ~-case :
    M ~ M' →
    Pointwise _~_ Ms Ms' →
    --------------------
    case M Ms ~ case M' Ms'

  ~-con : ∀ {K} →
    ---------
    con K  ~ con K

  ~-builtin : ∀ {b} →
    ---------------------
    builtin b ~ builtin b

  ~-error :
    ---------------------
    error ~ error

-- TODO: ~-refl is implied by the compatibility rules
```

## Properties

The relation is compatible with term constructors.

```
~-compat : TermCompatible _~_
~-compat = record
  { compat-var = ~-var
  ; compat-ƛ = ~-lam
  ; compat-· = ~-app
  ; compat-force = ~-force
  ; compat-delay = ~-delay
  ; compat-constr = ~-constr
  ; compat-case = ~-case
  ; compat-con = ~-con
  ; compat-builtin = ~-builtin
  ; compat-error = ~-error
  }
```

## Structures

For a fixed `X : ℕ`, `_~_` is a setoid, allowing to use equational reasoning notation:


```
open import Relation.Binary

~-setoid : ℕ → Setoid _ _
~-setoid X = record
  { Carrier = X ⊢
  ; _≈_ = _~_
  ; isEquivalence = record
    { refl = ~-refl
    ; sym = ~-sym
    ; trans = ~-trans
    }
  }
```

## Examples

```
-- open import VerifiedCompilation.UCaseReduce.Inductive
-- 
-- ~-pw-refl : Pointwise _~_ Ms Ms
-- ~-pw-refl {Ms = []} = []
-- ~-pw-refl {Ms = _ ∷ _} = ~-refl ∷ ~-pw-refl
-- 
-- refl-~-refl : M ≡ M' → M ~ M'
-- refl-~-refl refl = ~-refl
-- 
-- M~M' : Ex.M ~ Ex.M'
-- M~M' = case-constr refl
-- 
-- _ : Ex.N ~ Ex.N'
-- _ = ~-trans
--       (~-case M~M' ~-pw-refl)
--       (case-constr refl)
```


## Soundness

To prove that, we require a few properties about `reduce`:

`reduce` is the identity when applied to a `case` of which the discriminee is not a constructor:

```
reduce-id : ∀{X} (M : X ⊢) → ¬ (caseᵖ (constrᵖ match match) match) M → reduce M ≡ M
reduce-id (` x) ¬cc = refl
reduce-id (ƛ M) ¬cc = refl
reduce-id (M · M₁) ¬cc = refl
reduce-id (force M) ¬cc = refl
reduce-id (delay M) ¬cc = refl
reduce-id (con x) ¬cc = refl
reduce-id (constr i xs) ¬cc = refl
reduce-id (builtin b) ¬cc = refl
reduce-id error ¬cc = refl
reduce-id (case M ts) ¬cc with M
... | ` x = refl
... | ƛ M₁ = refl
... | M₁ · M₂ = refl
... | force M₁ = refl
... | delay M₁ = refl
... | con x = refl
... | builtin b = refl
... | error = refl
... | case _ _ = refl
... | constr _ _ with ¬cc inhabitant
... | ()
```

The normalisation rule is in the relation:

```
reduce-~ : ∀ {M : X ⊢} → M ~ reduce M
reduce-~ {M = M} with case? (constr? ⋯ ⋯) ⋯ M
... | no ¬P
  rewrite (reduce-id _ ¬P) = ~-refl
... | yes (case! (constr! (match! i) (match! Ns)) (match! Ms))
  with lookup? i Ms in eq
... | just M = case-constr eq
... | nothing = ~-refl
```

And therefore so is `norm`

```
norm-∼ : M ~ norm M
norm-∼ = ↑-extensive
  where open Extensive _~_ ~-trans ~-compat reduce reduce-~
```

We can then prove soundness:

```
sound : ∀ {X} {M M' : X ⊢} → CaseReduce M M' → M ~ M'
sound {X} {M} {M'} CaseReduceMM' =
  begin
    M
  ≈⟨ norm-∼ ⟩
    norm M
  ≡⟨ CaseReduceMM' ⟩
    norm M'
  ≈⟨ ~-sym norm-∼ ⟩
    M'
  ∎
  where open Reasoning (~-setoid X)
```

## Completeness

### Properties of `iterApp`:

```
iterApp-norm : ∀ (N : X ⊢) Ms → norm (iterApp N Ms) ≡ iterApp (norm N) (reduce ↑* Ms)
iterApp-norm _ [] = refl
iterApp-norm _ (_ ∷ Ts) = iterApp-norm _ Ts

iterApp-≡ :
  CaseReduce M M' →
  Pointwise CaseReduce Ms Ms' →
  CaseReduce (iterApp M Ms) (iterApp M' Ms')
iterApp-≡ M≡M' [] = M≡M'
iterApp-≡ M≡M' (N≡N' ∷ xs) = iterApp-≡ (cong₂ _·_ M≡M' N≡N') xs
  
```

### Properties of `lookup?`

It doesn't matter if you `lookup?` first and then normalise or the other way round:

```
lookup-norm : ∀ {j} {Ts} {T : X ⊢} →
  lookup? j Ts ≡ just T →
  lookup? j (norm* Ts) ≡ just (norm T)
lookup-norm {Ts = []} ()
lookup-norm {j = 0} {Ts = T ∷ Ts} refl = refl
lookup-norm {j = suc i} {Ts = T ∷ Ts} eq = lookup-norm {j = i} {Ts = Ts} eq
```

## A single rewrite is in the relation

One step of case-reduce is sound w.r.t `_≡_`:

```
case-constr-≡-c : ∀ {j : ℕ} {Ts} {T : X ⊢} (Us : List (X ⊢)) →
  lookup? j Ts ≡ just T →
  -----------------------
  CaseReduce (case (constr j Us) Ts) (iterApp T Us)
case-constr-≡-c {_} {j} {Ts} {T} Us eq
  rewrite (lookup-norm {j = j} {Ts = Ts} eq)
  rewrite iterApp-norm T Us = refl

```

```
pw-≡ : Pointwise CaseReduce Ms Ms' → norm* Ms ≡ norm* Ms'
pw-≡ [] = refl
pw-≡ (M≡M' ∷ MsMs') rewrite M≡M' rewrite pw-≡ MsMs' = refl

constr-≡ : Pointwise CaseReduce Ms Ms' → CaseReduce (constr i Ms) (constr i Ms')
constr-≡ MsMs' rewrite pw-≡ MsMs' = refl

case-≡ : CaseReduce M M' → Pointwise CaseReduce Ms Ms' → CaseReduce (case M Ms) (case M' Ms')
case-≡ MM' MsMs' rewrite MM' rewrite (pw-≡ MsMs') = refl

complete : M ~ M' → CaseReduce M M'
complete* : Pointwise _~_ Ms Ms' → Pointwise CaseReduce Ms Ms'

complete (case-constr {Ns} {N} {Ms} {i = i} lookup≡) = case-constr-≡-c {j = i} {Ts = Ns} Ms lookup≡

complete ~-refl = refl
complete (~-trans P Q) = trans (complete P) (complete Q)
complete (~-sym P) = sym (complete P)

complete ~-var = refl
complete (~-lam P) = cong ƛ (complete P)
complete (~-app P Q) = cong₂ _·_ (complete P) (complete Q)
complete (~-force P) = cong force (complete P)
complete (~-delay P) = cong delay (complete P)
complete (~-constr Ps) = constr-≡ (complete* Ps)
complete (~-case {M = M} {M' = M'} P Ps) = case-≡ {M = M} {M' = M'} (complete P) (complete* Ps)
complete ~-con = refl
complete ~-builtin = refl
complete ~-error = refl

complete* [] = []
complete* (P ∷ Ps) = complete P ∷ complete* Ps
```


New reduce, that includes casing on constants:

```
```

## Old translation relation


`norm` is sound with respect to the inductive translation relation

```
open Translation renaming (match to compat; istranslation to rule)
open TransMatch
open Pointwise

open import VerifiedCompilation.UCaseReduce.Inductive using (CaseReduce'; casereduce')

reduce-case : ∀{X} (M : X ⊢) (Ms) → ¬ constrᵖ match match M → reduce (case M Ms) ≡ case M Ms
reduce-case (` x) _ _ = refl
reduce-case (ƛ M₁) _ _ = refl
reduce-case (M₁ · M₂) _ _ = refl
reduce-case (force M₁) _ _ = refl
reduce-case (delay M₁) _ _ = refl
reduce-case (con x) _ _ = refl
reduce-case (case M₁ ts) _ _ = refl
reduce-case (builtin b) _ _ = refl
reduce-case error _ _ = refl
reduce-case (constr i xs) _ ¬constr with ¬constr inhabitant
... | ()



norm-CR : ∀ {X} (M : X ⊢) → Translation CaseReduce' M (norm M)
norm-CR* : ∀ {X} (Ms : List (X ⊢)) → Pointwise (Translation CaseReduce') Ms (reduce ↑* Ms)

norm-CR (` x) = compat var
norm-CR (ƛ M) = compat (ƛ (norm-CR M))
norm-CR (M₁ · M₂) = compat (app (norm-CR M₁) (norm-CR M₂))
norm-CR (force M₁) = compat (force (norm-CR M₁))
norm-CR (delay M₁) = compat (delay (norm-CR M₁))
norm-CR (con x) = compat con
norm-CR (constr i Ms) = compat (constr (norm-CR* Ms))
norm-CR (builtin b) = compat builtin
norm-CR error = compat error
norm-CR (case M Ms)
  with reduce ↑* Ms in eqMs | norm M in eqM
... | Ms' | M'
  with constr? ⋯ ⋯ M'
... | no ¬constr
        rewrite reduce-case M' Ms' ¬constr | sym eqM | sym eqMs
        = compat (case (norm-CR* Ms) (norm-CR M))
... | yes (constr! (match! i) (match! Ns))
  with lookup? i Ms' in eq-i
... | nothing
        rewrite sym eqM | sym eqMs
        = compat (case (norm-CR* Ms) (norm-CR M))
... | just N
        rewrite sym eqMs
        = rule (casereduce'
            (subst (Translation CaseReduce' M) eqM (norm-CR M))
            (norm-CR* Ms)
            eq-i
          )

norm-CR* [] = []
norm-CR* (M ∷ Ms) = norm-CR M ∷ norm-CR* Ms
```

