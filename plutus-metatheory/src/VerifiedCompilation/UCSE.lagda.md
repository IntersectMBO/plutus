---
title: VerifiedCompilation.UCSE
layout: page
---

# Common Subexpression Elimination Translation Phase
```
module VerifiedCompilation.UCSE where

```
## Imports

```
open import Untyped.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.UntypedViews
open import VerifiedCompilation.UntypedTranslation using (Translation; TransMatch; translation?; Relation)
open import Relation.Nullary using (_×-dec_)
open import Data.Product using (_,_)
import Relation.Binary as Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error; Let_In_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; suc; zero)
open import Data.Empty using (⊥)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Untyped.RenamingSubstitution using (_[_])
open import Untyped.Purity using (Pure; isPure?)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; pcePointwise; DecidableCE; CseT; isProof?)
open import Data.Bool.Base using (Bool; false; true)
open import Data.List hiding ([_])
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Data.List.Relation.Unary.Any using (Any; any?)

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
   as witnessed by `OccursOnExecPath`, a predicate that holds when a variable lies
   on at least one execution path through a term. This guarantees soundness: the
   transformed term is no less strict than the original.

```

private variable
  n : ℕ

data OccursOnExecPath (var : Fin n) : n ⊢ → Set where
  here : OccursOnExecPath var (` var)
  underForce
    : {term : n ⊢}
    → OccursOnExecPath var term
    → OccursOnExecPath var (force term)
  underAppLhs
    : {term₁ term₂ : n ⊢}
    → OccursOnExecPath var term₁
    → OccursOnExecPath var (term₁ · term₂) 
  underAppRhs
    : {term₁ term₂ : n ⊢}
    → OccursOnExecPath var term₂
    → OccursOnExecPath var (term₁ · term₂) 
  underConstr
    : {i : ℕ} {args : List (n ⊢)}
    → Any (OccursOnExecPath var) args
    → OccursOnExecPath var (constr i args)
  underScrut
    : {scrut : n ⊢} {branches : List (n ⊢)}
    → OccursOnExecPath var scrut
    → OccursOnExecPath var (case scrut branches)
  underLet
    : {term₁ : n ⊢} {term₂ : suc n ⊢}
    → OccursOnExecPath (suc var) term₂
    → OccursOnExecPath var (Let term₁ In term₂)

data UCSE : Relation where
  cse : {x' : suc n ⊢} {x e : n ⊢}
    → OccursOnExecPath zero x'
    → Translation UCSE x (x' [ e ])
    → UCSE x (Let e In x')

UntypedCSE : (ast : n ⊢) → (ast' : n ⊢) → Set
UntypedCSE = Translation UCSE

```

## Decision Procedure

`occursOnExecPath?` decides `OccursOnExecPath`. Most term forms have a unique strict
sub-term, so the procedure is a straightforward structural recursion. The application
case is the exception: `underAppLhs` and `underAppRhs` can both hold simultaneously
when the variable appears in both sides, making the proposition non-unique. The
procedure resolves this ambiguity by always preferring `underAppLhs`. If the LHS
witness exists it is returned immediately, and `underAppRhs` is only tried when the
LHS fails.

`isUCSE?` decides `UCSE` by checking that the output is a `let`-binding, that `zero`
occurs on an execution path through the body, and that the result of back-substitution
is accepted by `isUntypedCSE?`.

```

{-# TERMINATING #-}
occursOnExecPath? : (v : Fin n) → (t : n ⊢) → Dec (OccursOnExecPath v t)
occursOnExecPath? v term with (Let? ⋯ In? ⋯) term
... | yes (Let! (match! rhs) In! (match! body)) with occursOnExecPath? (suc v) body
...   | yes p = yes (underLet p)
...   | no ¬p with occursOnExecPath? v rhs
...     | yes q = yes (underAppRhs q) 
...     | no ¬q = no λ {(underAppRhs x) → ¬q x
                      ; (underLet x) → ¬p x
                      }
occursOnExecPath? v term
  | no ¬letMatch with (`? ⋯) term
... | yes (`! (match! var)) with v Data.Fin.≟ var
...   | yes refl = yes here
...   | no ¬p = no λ { here → ¬p refl }
occursOnExecPath? v term
  | no ¬varMatch
  | no ¬letMatch with (force? ⋯) term
... | yes (force! (match! t)) with occursOnExecPath? v t
...   | yes p = yes (underForce p)
...   | no ¬p = no λ { (underForce x) → ¬p x } 
occursOnExecPath? v term
  | no ¬forceMatch
  | no ¬varMatch
  | no ¬letMatch with (constr? ⋯ ⋯) term
... | yes (constr! i (match! ts)) with any? (occursOnExecPath? v) ts
...   | yes p = yes (underConstr p)
...   | no ¬p = no λ { (underConstr x) → ¬p x }
occursOnExecPath? v term
  | no ¬constrMatch
  | no ¬forceMatch
  | no ¬varMatch
  | no ¬letMatch with (case? ⋯ ⋯) term
... | yes (case! (match! scrut) _) with occursOnExecPath? v scrut
...   | yes p = yes (underScrut p)
...   | no ¬p = no λ { (underScrut x) → ¬p x }
occursOnExecPath? v term
  | no ¬caseMatch
  | no ¬constrMatch
  | no ¬forceMatch
  | no ¬varMatch
  | no ¬letMatch with (⋯ ·? ⋯) term
... | yes (match! t₁ ·! match! t₂) with occursOnExecPath? v t₁ | occursOnExecPath? v t₂
...   | yes p | _     = yes (underAppLhs p)
...   | _     | yes q = yes (underAppRhs q)
...   | no ¬p | no ¬q = no λ {(underAppLhs x) → ¬p x
                            ; (underAppRhs x) → ¬q x
                            ; (underLet x) → ¬caseMatch (Let! match! t₂ In! match! _)
                            }
occursOnExecPath? v term
  | no ¬appMatch
  | no ¬caseMatch
  | no ¬constrMatch
  | no ¬forceMatch
  | no ¬varMatch
  | no ¬letMatch = no λ
    { here → ¬caseMatch (`! (match! v))
    ; (underForce x) → ¬constrMatch (force! (match! _))
    ; (underAppLhs x) → ¬letMatch (match! _ ·! match! _)
    ; (underAppRhs x) → ¬letMatch (match! _ ·! match! _)
    ; (underConstr x) → ¬forceMatch (constr! (match! _) (match! _))
    ; (underScrut x) → ¬varMatch (case! (match! _) (match! _))
    ; (underLet x) → ¬letMatch (match! (ƛ _) ·! match! _) 
    }


isUntypedCSE? : DecidableCE (Translation UCSE {n})

{-# TERMINATING #-}
isUCSE? : DecidableCE (UCSE {n})

isUCSE? ast₁ ast₂ with (Let? ⋯ In? ⋯) ast₂ 
... | no ¬letMatch = ce (λ { (cse x x₁) → ¬letMatch inhabitant}) CseT ast₁ ast₂
... | yes (Let! match! rhs In! match! body) with occursOnExecPath? zero body
...   | no ¬onPath = ce (λ { (cse x x₁) → ¬onPath x }) CseT ast₁ ast₂
...   | yes onPath with (isUntypedCSE? ast₁ (body [ rhs ]))
...     | ce ¬isCSE tag t₁ t₂ = ce (λ { (cse x x₁) → ¬isCSE x₁ }) tag t₁ t₂
...     | proof isCSE = proof (cse onPath isCSE)

isUntypedCSE? = translation? CseT isUCSE?
```

## Tests

A few unit tests which check that the decision procedure works as expected.

The third test shows that `OccursOnExecPath` catches an unsound transformation.

```

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
