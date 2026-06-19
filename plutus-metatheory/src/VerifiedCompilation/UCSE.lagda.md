---
title: VerifiedCompilation.UCSE
layout: page
---

# CSE and Hoist Polymorphic Builtins
```
module VerifiedCompilation.UCSE where

```
## Imports

```
open import VerifiedCompilation.UntypedViews
open import VerifiedCompilation.UntypedTranslation using (Translation; TransMatch; translation?; Relation)
open import VerifiedCompilation.UntypedViews
import Relation.Binary as Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_; from-yes)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error; Let_In_; let₂)
open import Builtin
open import Untyped.RenamingSubstitution
open import Untyped.Strictness
open import Untyped.Purity using (Pure; isPure?)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Fin using (Fin; suc; zero; #_)
open import Untyped.RenamingSubstitution using (_[_])
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; pcePointwise; DecidableCE; CseT; isProof?)
open import Data.Bool.Base using (Bool; false; true)
open import Data.List hiding ([_])
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (_×-dec_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (∃ ; _,_)
open import Untyped.Equality using (_≟_)

```
## Description

This module is required to certify that an application of CSE doesn't break the
semantics; we are explicitly not evaluating whether the particular choice of
sub-expression was a "good" choice.

The `UCSE` translation relation has a single constructor `cse`. A term `x` translates
to `Let e In x'` when:

1. Substituting `e` back into `x'` yields a term that `UCSE`-translates from `x`,
   so the transformation is locally invertible up to further CSE steps.

2. `zero` (the variable bound by the `let`) lies on an execution path through `x'`,
   as witnessed by `∈↓`, a predicate that holds when a variable lies
   on at least one execution path through a term. This guarantees soundness: the
   transformed term is no less strict than the original.

```

private variable
  n : ℕ

data UCSE : Relation where
  cse : {x' : suc n ⊢} {x e : n ⊢}
    → zero ∈↓ x'
    → Translation UCSE x (x' [ e ])
    → UCSE x (Let e In x')

UntypedCSE : (ast : n ⊢) → (ast' : n ⊢) → Set
UntypedCSE = Translation UCSE

```

## Decision Procedure

`isUCSE?` decides `UCSE` by checking that the output is a `let`-binding, that `zero`
occurs on an execution path through the body, and that the result of back-substitution
is accepted by `isUntypedCSE?`.

```

isUntypedCSE? : DecidableCE (Translation UCSE {n})

{-# TERMINATING #-}
isUCSE? : DecidableCE (UCSE {n})

isUCSE? ast₁ ast₂ with (Let? ⋯ In? ⋯) ast₂ 
... | no ¬letMatch = ce (λ { (cse x x₁) → ¬letMatch inhabitant}) CseT ast₁ ast₂
... | yes (Let! match! rhs In! match! body) with zero ∈↓? body
...   | no ¬onPath = ce (λ { (cse x x₁) → ¬onPath x }) CseT ast₁ ast₂
...   | yes onPath with (isUntypedCSE? ast₁ (body [ rhs ]))
...     | ce ¬isCSE tag t₁ t₂ = ce (λ { (cse x x₁) → ¬isCSE x₁ }) tag t₁ t₂
...     | proof isCSE = proof (cse onPath isCSE)

isUntypedCSE? = translation? CseT isUCSE?
```

## Hoisting polymorphic built-ins

This pass differs slightly from CSE in two ways:

1. it produces multi-lets, i.e.

   (λ (λ (...)) · M₀ · ... · Mₙ

2. all produced lets appear at the very top of the post-term.

3. Only partially applied built-ins are lifted (always pure)


### Application contexts

For describing the nested let structure we need to keep track of an application
context, represented as a list of terms. We sometimes need to apply a function
to those arguments.

```
applyN : ∀ {X} → X ⊢ → List (X ⊢) → X ⊢
applyN M [] = M
applyN M (N ∷ Ns) = applyN (M · N) Ns
```

The relation keeps a list of function arguments as extra index, similar to the
zipper of the inliner relation:

```
data HoistPoly {X : ℕ} : List (X ⊢) → X ⊢ → X ⊢ → Set where
  let-·
    : {Ls : List (X ⊢)}
    → {M N L : X ⊢}
    → HoistPoly (L ∷ Ls) M N
    ------------------------
    → HoistPoly Ls M (N · L)

  let-ƛ
    : {Ls : List (X ⊢)}
    → {M L : X ⊢}
    → {N : suc X ⊢}
    → Pure L
    → HoistPoly Ls M (N [ L ])
    ----------------------------
    → HoistPoly (L ∷ Ls) M (ƛ N)

  refl
    : {Ls : List (X ⊢)}
    → {M N : X ⊢}
    → M ≡ applyN N Ls
    → HoistPoly Ls M N
```

The first two rules traverse the structure of nested lets, by collecting the
arguments and traversing the corresponding lambdas. At each lambda, we
substitute the bound term. Once we traversed the lets, we simply require terms
to be equal.

### Decision procedure

Termination argument: we traverse a finite amount of lets on the top-level this
would be easier to prove if we keep a substitution environment in the relation
instead of directly susbtituting having a rule for the variable case that looks
in that environment. That way, size(M) + size(N) decreases in every rule.

```
{-# TERMINATING #-}
dec-hoist : {X : ℕ} (Ls : List (X ⊢)) (M N : X ⊢) → Dec (HoistPoly Ls M N)
dec-hoist Ls M N
  with (ƛ? ⋯) N ×-dec (⋯ ∷? ⋯) Ls
dec-hoist _ M _ | yes (ƛ! (match! N) , (match! L) ∷! (match! Ls) )
  with isPure? L ×-dec dec-hoist Ls M (N [ L ])
... | yes (pure , hoist) = yes (let-ƛ pure hoist)
... | no ¬pure-hoist
  with M ≟ applyN (ƛ N) (L ∷ Ls)
... | yes refl = yes (refl refl)
... | no ¬refl = no λ { (let-ƛ pure M~N[L]) → ¬pure-hoist (pure , M~N[L])
                      ; (refl refl) → ¬refl refl
                      }
dec-hoist Ls M N | no ¬ƛ∷ 
  with (⋯ ·? ⋯) N
... | yes (match! N ·! match! L)
  with dec-hoist (L ∷ Ls) M N
... | yes M~N = yes (let-· M~N)
... | no ¬M~N
  with M ≟ applyN (N · L) Ls
... | yes refl = yes (refl refl)
... | no ¬refl = no λ { (let-· M~N) → ¬M~N M~N
                      ; (refl refl) → ¬refl refl}

dec-hoist Ls M N | no ¬ƛ∷ | no ¬·
  with M ≟ (applyN N Ls)
... | yes refl = yes (refl refl)

... | no ¬refl = no λ { (let-ƛ pure M~N[L]) → ¬ƛ∷ inhabitant
                      ; (let-· _) → ¬· inhabitant
                      ; (refl refl) → ¬refl refl
                      }

```

### Counting optimization sites

The amount of expressions that appear hoisted in the post-term:

```
polyNumSites : ∀ {X} {Ls : List (X ⊢)} {M N : X ⊢} → HoistPoly Ls M N → ℕ
polyNumSites (let-· p) = 1 + polyNumSites p
polyNumSites (let-ƛ x p) = 0
polyNumSites (refl x) = 0
```

## Tests

A few unit tests which check that the decision procedure works as expected.

The third test shows that the strictness condition catches an unsound transformation.

```

private

  M₁ : 1 ⊢
  M₁ = constr 0 [] · constr 0 []

  N₁ : 1 ⊢
  N₁ = Let constr 0 [] In ` zero · ` zero

  _ : isProof? (isUntypedCSE? M₁ N₁) ≡ true
  _ = refl

  M₂ : 1 ⊢
  M₂ = Let constr 0 [] In ` zero

  N₂ : 1 ⊢
  N₂ = Let constr 0 [] In ` zero

  _ : isProof? (isUntypedCSE? M₂ N₂) ≡ true
  _ = refl

  M₃ : 1 ⊢
  M₃ = constr 0 []

  N₃ : 1 ⊢
  N₃ = Let error In constr 0 []

  _ : isProof? (isUntypedCSE? M₃ N₃) ≡ false
  _ = refl
```

Tests for HoistPoly

```
private
  pre : 2 ⊢
  pre = force (builtin ifThenElse)
        · (` (# 0))
        · (constr 0 [])
        · (force (builtin trace)
           · (` (# 1))
           · (constr 1 [])
          )

  post : 2 ⊢
  post = let₂
        (force (builtin ifThenElse))
        (force (builtin trace))
        ( ` (# 1) -- ifThenElse
        · ` (# 2)
        · constr 0 []
        · ( ` (# 0) -- trace
          · ` (# 3)
          · constr 1 []
          )
        )

  open Pure
  pure₁ : Pure {2} (force (builtin ifThenElse))
  pure₁ = unsat-builtin₀₋₁ refl builtin
  pure₂ : Pure {2} (force (builtin trace))
  pure₂ = unsat-builtin₀₋₁ refl builtin

  -- manual derivation
  pre-post : HoistPoly [] pre post
  pre-post = let-· (let-· (let-ƛ pure₁ (let-ƛ pure₂ (refl refl))))

  -- decision procedure
  pre-post' : HoistPoly [] pre post
  pre-post' = from-yes (dec-hoist [] pre post)
```
