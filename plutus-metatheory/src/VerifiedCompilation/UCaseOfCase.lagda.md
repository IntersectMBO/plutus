---
title: VerifiedCompilation.UCaseOfCase
layout: page
---

# Case of Case transformation
```
module VerifiedCompilation.UCaseOfCase where
```
## Imports

```
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Fin using (suc; zero)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Product using (_×_; proj₁; proj₂; _,_; ∃)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.All using (All; all?)

open import Relation.Nullary using (Dec; yes; no; _×-dec_; _⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Untyped
open import Builtin using (Builtin; ifThenElse)
open import Untyped.Equality
open import Untyped.Transform
open import Untyped.Relation.Binary hiding (Pointwise)
open import Untyped.Relation.Binary.Modular
open import VerifiedCompilation.UntypedViews
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; CaseOfCaseT; Proof?; isProof?)
```

This pass will build on the case-reduce optimisation.

```
import VerifiedCompilation.UCaseReduce as CaseReduce
```

## Generalized variables

Note that for inductives, these variables become an _index_, not a parameter!
This influences the position where this variable occurs in the inductive type.

```
private variable
  n : ℕ

  M N L : n ⊢
  Ms Ns Ts inner outer : List (n ⊢)
  M' N' L' T' : n ⊢
  K : TmCon
```


## Translation Relation

There are two rewrite rules for this pass.

### Rule CaseCase

This rule considers nested case expressions of the form `case (case M inner)
outer` and turns the inner case inside-out, pushing a copy of the outer case in
each inner branch. Those cases inside are then further reduced with the
`CaseReduce` pass. For example:

```text
  case (case M [const integer 0, const integer 0, const integer 7]) [True, False]

  ⟶⟨ case-case ⟩

  case M [ case (const integer 0) [True, False]
         , case (const integer 0) [True, False]
         , case (const integer 7) [True, False]
         ]

  ⟶⟨ case-reduce ⟩

  case M [ True
         , True
         , case 7 [True, False]
         ]
```

Note that the final case could not be reduced.

As a precondition, the inner branches `Ms` must be either constants or
constructors. We call those terms scrutinizable.

```
data Scrutinizable : n ⊢ → Set where
  scrut-constr :
       ∀ {i} {Ms : List (n ⊢)}
    →  ---------------------------
       Scrutinizable (constr i Ms)

  scrut-con :
       ∀ {K : TmCon}
    →  -------------------------
       Scrutinizable (con {n} K)
```

The pass tries to case-reduce the resulting inner cases.

```
TryReduceStep : Relation
TryReduceStep = (CaseReduce.Reduction ⊕ Reflexivity) _≡_

tryReduceStep : (M : n ⊢) → ∃ λ M' → TryReduceStep M M'
tryReduceStep M =
  maybe′
    (λ (M' , M⟶M') → (M' , inl M⟶M'))
    (M , inr reflF)
    (CaseReduce.reduce M)

tryReduceStep' : n ⊢ → n ⊢
tryReduceStep' M = proj₁ (tryReduceStep M)
```

Each branch `N` in the inner `case` must be scrutinizable, so that they can be
used as scrutinee in the cases in each resulting branch. Each `N` must be
transformed to a case that scrutinizes `N` and then uses the original branches
`outers`.

The `CaseCase` rule captures the reduction of the form `case (case M inner) outer`.

```
data CaseCase (@++ R : Relation) : Relation where
  caseCase :
    ∀ {n} {M : n ⊢} {inner outer Ls' : List (n ⊢)}
    → All Scrutinizable inner -- TODO, this is probably implied by the next premise
    → Pointwise (λ N L' → TryReduceStep (case N outer) L') inner Ls'
    -------------------------------------------------------------
    → CaseCase R
        (case (case M inner) outer)
        (case M Ls')
```


### Rule CaseIf

The `CaseIf` rule is similar, but deals with the form `case (force ifThenElse · M · N · L) Ts`

```
data CaseIf (@++ R : Relation) : Relation where
  caseIf :
    ∀ {n} {M N L caseN' caseL' : n ⊢} {Ts : List (n ⊢)}
    → Scrutinizable N
    → Scrutinizable L
    → TryReduceStep (case N Ts) caseN'
    → TryReduceStep (case L Ts) caseL'
    ----------------------------------------
    → CaseIf R
        (case
           (
             force (builtin ifThenElse)
             · M
             · N
             · L
           )
           Ts
        )
        (force
          (
             force (builtin ifThenElse)
             · M
             · delay caseN'
             · delay caseL'
          )
        )
```

## Running the pass

```
scrutinizable? : (M : n ⊢) → Dec (Scrutinizable M)
scrutinizable? M
  with constr? ⋯ ⋯ M ⊎-dec con? ⋯ M
... | no ¬p = no λ { scrut-constr → ¬p (inj₁ inhabitant)
                   ; scrut-con    → ¬p (inj₂ inhabitant)
                   }
... | yes (inj₁ (constr! (match! i) (match! args))) = yes scrut-constr
... | yes (inj₂ (con! K)) = yes scrut-con
```

```
-- TODO, this function must exist already somewhere in stdlib
map-∃ : ∀ {A B : Set} {P : A → B → Set}
        → ((x : A) → ∃ λ y → P x y)
        → ((xs : List A) → ∃ λ ys → Pointwise P xs ys)
map-∃ f [] = [] , []
map-∃ f (x ∷ xs)
  with map-∃ f xs | f x
... | ys , xs-ys | y , x-y = y ∷ ys , x-y ∷ xs-ys
```

```
private variable
  R : Relation

step-CaseCase : (M : n ⊢) → Maybe (∃ λ M' → CaseCase _≡_ M M')
step-CaseCase M
  with (case? (case? ⋯ ⋯) ⋯) M
... | no _ = nothing
... | yes (case! (case! (match! M) (match! inner)) (match! outer))
  with all? scrutinizable?  inner
... | no _ = nothing
... | yes P
  with map-∃ (λ N → tryReduceStep (case N outer)) inner
... | Ls' , cases⟶Ls' =
  just
    ( case M Ls'
    , caseCase P cases⟶Ls'
    )

step-CaseIf : (M : n ⊢) → Maybe (∃ λ M' → CaseIf _≡_ M M')
step-CaseIf M
  with
    (case?
      (force? (builtin? (_≟_ ifThenElse)) ·? ⋯ ·? ⋯ ·? ⋯)
      ⋯
    ) M
... | no _ = nothing
... | yes (case!
             (force! (builtin! refl) ·! match! M ·! match! N ·! match! L)
             (match! Ts)
          )
  with scrutinizable? N
       ×-dec scrutinizable? L
... | no _ = nothing
... | yes (sN , sL)
  with
    tryReduceStep (case N Ts)
    | tryReduceStep (case L Ts)
... | N' , caseN⟶N' | L' , caseL⟶L' = just (_ , caseIf sN sL caseN⟶N' caseL⟶L')
```

The complete pass

```
reduce : (M : n ⊢) → Maybe (∃ λ M' → (CaseCase ⊕ CaseIf) _≡_ M M')
reduce = step-CaseCase <|> step-CaseIf

pass : n ⊢ → n ⊢
pass = refine? reduce ↑?_

CaseOfCase : Relation
CaseOfCase M M' = pass M ≡ M'

decide : (M M' : n ⊢) → ProofOrCE (CaseOfCase M M')
decide M M' with pass M ≟ M'
... | yes P = proof P
... | no ¬P  = ce ¬P CaseOfCaseT M M'
```


## Examples

case-case
```
private module Examples where

  M₁ : 0 ⊢
  M₁ = case
        (case
          (constr 1 [])
          ( constr 0 []
          ∷ constr 1 []
          ∷ []
          )
        )
        ( constr 42 []
        ∷ constr 43 []
        ∷ []
        )

  M₁' : 0 ⊢
  M₁' =
    case
      (constr 1 [])
      ( (constr 42 [])
      ∷ (constr 43 [])
      ∷ []
      )

  M₁-M₁' : isProof? (decide M₁ M₁') ≡ true
  M₁-M₁' = refl
```

case-if

```
  sopTrue : ∀ {m} → m ⊢
  sopFalse : ∀ {m} → m ⊢
  sopTrue = constr 0 []
  sopFalse = constr 1 []

  M₂ : 0 ⊢
  M₂ =
    ƛ
      (case
        (force (builtin ifThenElse) · ` zero · sopTrue · sopFalse)
        (
          con-integer 1
          ∷ con-integer 2
          ∷ []
        )
      )

  M₂' : 0 ⊢
  M₂' =
    ƛ
      (force
        (force (builtin ifThenElse)
          · ` zero
          · delay (con-integer 1)
          · delay (con-integer 2)
        )
      )

  M₂-M₂' : isProof? (decide M₂ M₂') ≡ true
  M₂-M₂' = refl

```
