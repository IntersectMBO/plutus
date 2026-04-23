---
title: VerifiedCompilation.UCaseReduce
layout: page
---

# Case-Reduce Translation Phase

This module defines two translation relations for the case-reduce pass:

- `Computational`: A "computational" relation that builds on a re-implementation
  of the compiler pass (`case-reduce` function below). The relation simply
  requires the reduced pre-term to be equal to the post-term. This was simpler
  than defining a decision procedure that compares pre- and post-term. The
  relation has a decision procedure.

- `CaseReduce`: An inductive relation, built using the generic building blocks
  from `Untyped.Relation.Modular`. It is an equivalence relation and therefore
  allows applying reduction rules in the reverse direction (which is not
  expected from the compiler pass). It also admits a decision procedure which
  works by case-reducing _both_ the pre-term and post-term.

The computational relation is closer to the compiler implementation, while the
inductive relation more general: it is an equivalence relation similar to the
one in the "A Tale of two Zippers" papers. The equivalence is more "obviously"
semantics preserving.

The computational relation is sound (but not complete) w.r.t. the inductive
equivalence relation.

```
module VerifiedCompilation.UCaseReduce where

```
## Imports

```

open import Data.Bool using (true; false; if_then_else_; Bool)
open import Data.Maybe
open import Data.List using (List; _∷_; []; [_])
open import Data.Product
open import Data.Unit using (tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin using (Fin)
open import Data.Integer using (ℤ ; +_; -[1+_])

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no; ¬_)

open import Untyped
open import Builtin.Constant.AtomicType
open import RawU using (tag2TyTag; tmCon; Tag)

open import Untyped.Equality
open import Untyped.Reduction using (iterApp)
open import Untyped.Relation
open import Untyped.Relation.Composable
open import Untyped.Transform
open Untyped.Transform.Refines?
open import Untyped.CEK using (lookup?)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; caseReduceT; Proof?; abort)
open import VerifiedCompilation.UntypedViews
open import Utils using () renaming (_,_ to _,,_; _∷_ to cons; [] to nil)

```
## Reduction Rules

These are the (single-step) reduction rules of the case-reduce pass, defined as
relation transformers so they can be composed for the inductive translation relation.

```
module Rules where

  private variable
    X : ℕ
    M N N₁ N₂ : X ⊢
    Ns Ms : List (X ⊢)
    i : ℕ

  data CaseConstr (@++ R : Relation) : Relation where
    case-constr :
      ∀ {X} {i} {N : X ⊢} {Ns Ms}
      → lookup? i Ns ≡ just N
      -----------------------------------------------------
      → CaseConstr R (case (constr i Ms) Ns) (iterApp N Ms)

  data CaseUnit (@++ R : Relation) : Relation where
    case-unit :
      ∀ {X} {N : X ⊢}
      ---------------------------------------------
      → CaseUnit R (case (con (tmCon unit tt)) [ N ]) N

  data CaseFalse₁ (@++ R : Relation) : Relation where
    case-false₁ :
      ∀ {X} {N : X ⊢}
      --------------------------------------------------
      → CaseFalse₁ R (case (con (tmCon bool false)) [ N ]) N

  data CaseBool (@++ R : Relation) : Relation where
    case-bool :
      ∀ {X} {b} {N₁ N₂ : X ⊢}
      -----------------------------------------------------------------------
      → CaseBool R (case (con (tmCon bool b)) (N₁ ∷ N₂ ∷ [])) (if b then N₂ else N₁)

  data CaseInteger (@++ R : Relation) : Relation where
    case-integer :
      ∀ {X n} {N : X ⊢} {Ns}
      → lookup? n Ns ≡ just N
      ---------------------------------------------------
      → CaseInteger R (case (con (tmCon integer (+ n))) Ns) N

  data CaseCons₁ (@++ R : Relation) : Relation where
    case-cons₁ :
      ∀ {X} {A x xs} {N : X ⊢}
      ----------------------------------------------------
      → CaseCons₁ R
          (case (con (tmCon (list A) (cons x xs))) (N ∷ []))
          (N · con (tmCon A x) · con (tmCon (list A) xs))

  data CaseCons₂ (@++ R : Relation) : Relation where
    case-cons₂ :
      ∀ {X} {A x xs} {N₁ N₂ : X ⊢}
      ----------------------------------------------------------
      → CaseCons₂ R
          (case (con (tmCon (list A) (cons x xs))) (N₁ ∷ N₂ ∷ []))
          (N₁ · con (tmCon A x) · con (tmCon (list A) xs))

  data CaseNil (@++ R : Relation) : Relation where
    case-nil :
      ∀ {X} {N₁ N₂ : X ⊢} {A}
      -----------------------------------------------------------
      → CaseNil R
          (case (con (tmCon (list A) nil)) (N₁ ∷ N₂ ∷ []))
          N₂

  data CasePair (@++ R : Relation) : Relation where
    case-pair :
      ∀ {X} {A B x y} {N : X ⊢}
      ----------------------------------------------------
      → CasePair R
          (case (con (tmCon (pair A B) (x ,, y ))) (N ∷ []))
          (N · con (tmCon A x) · con (tmCon B y))

open Rules
```

## Inductive translation relation

Combining the reduction rules:

```
Reduction : RelationT
Reduction
  = CaseConstr
  + CaseUnit
  + CaseFalse₁
  + CaseBool
  + CaseInteger
  + CaseCons₁
  + CaseCons₂
  + CaseNil
  + CasePair
```

The full translation relation is closed under the reduction rules, compatibility
rules, and equivalence rules:

```
CaseReduce : Relation
CaseReduce = Mu (Reduction + CompatTerm + Transitivity + Symmetry + Reflexivity)
```

Pattern synonyms for constructors:

```
pattern cr-reduction p = fix (inl p)
pattern cr-compat p    = fix (inr (inl p))
pattern cr-trans p q   = fix (inr (inr (inl (transF p q))))
pattern cr-sym p       = fix (inr (inr (inr (inl (symF p)))))
pattern cr-refl        = fix (inr (inr (inr (inr reflF))))
```

Convenient helpers

```
cr-refl' :
  ∀ {X} {M N : X ⊢}
  → M ≡ N
  → CaseReduce M N
cr-refl' refl = cr-refl

cr-refl* :
  ∀ {X} {Ms : List (X ⊢)}
  → Pointwise CaseReduce Ms Ms
cr-refl* = pointwise-refl {R = CaseReduce} cr-refl

cr-TermCompat : TermCompatible CaseReduce
cr-TermCompat = CompatTerm-TermCompatible cr-compat
```

Testing the relation:

```
private module Test where
  M : 0 ⊢
  M = case (constr 0 []) (constr 0 [] ∷ constr 1 [] ∷ [])

  M' : 0 ⊢
  M' = constr 0 []

  MM' : CaseReduce M M'
  MM' = cr-reduction (inl (case-constr refl))


  N : 0 ⊢
  N = case M (constr 42 [] ∷ [])
  N' : 0 ⊢
  N' = constr 42 []

  _ : CaseReduce N N'
  _ =
    cr-trans
      (compat-case MM' cr-refl*)
      (cr-reduction (inl (case-constr refl)))
    where
      open TermCompatible cr-TermCompat
```

## Computational translation relation

For each of the inductive reduction rules, we give a corresponding partial
function, which also witnesses the proof of the reduction rule when it succeeds
(this comes in handy when proving soundness w.r.t the inductive translation
relation later on)

```
private variable
  R : Relation
  X : ℕ

red-constr : (M : X ⊢) → Maybe (∃ λ M' → CaseConstr R M M')
red-constr M
  with (case? (constr? ⋯ ⋯) ⋯) M
... | no _ = nothing
... | yes (case! (constr! (match! i) (match! Ms)) (match! Ns))
  with lookup? i Ns in eq
... | nothing = nothing
... | just N = just (iterApp N Ms , case-constr eq)

red-unit : (M : X ⊢) → Maybe (∃ λ M' → CaseUnit R M M')
red-unit M
  with (case? (con? (tmCon? unit ⋯)) (⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon! (match! v))) (match! N ∷! []!))
  = just (N , case-unit)

red-false₁ : (M : X ⊢) → Maybe (∃ λ M' → CaseFalse₁ R M M')
red-false₁ M
  with (case? (con? (tmCon? bool (_≟_ false))) (⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon! refl)) (match! N ∷! []!)) = just (N , case-false₁)

red-bool : (M : X ⊢) → Maybe (∃ λ M' → CaseBool R M M')
red-bool M
  with (case? (con? (tmCon? bool ⋯)) (⋯ ∷? ⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon! (match! b))) (match! N₁ ∷! match! N₂ ∷! []!))
    = just ((if b then N₂ else N₁) , case-bool)

red-integer : (M : X ⊢) → Maybe (∃ λ M' → CaseInteger R M M')
red-integer M
  with (case? (con? (tmCon? integer pos?)) ⋯) M
... | no _ = nothing
... | yes (case! (con! (tmCon! (pos! n))) (match! Ns))
  with lookup? n Ns in eq
... | nothing = nothing
... | just N = just (N , case-integer eq)

red-cons₁ : (M : X ⊢) → Maybe (∃ λ M' → CaseCons₁ R M M')
red-cons₁ M with
  (case? (con? (tmCon-list? (λ A xs → cons? ⋯ ⋯ xs))) (⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon-list! (cons! (match! x) (match! xs)))) (match! N ∷! []!)) =
  just (N · con (tmCon _ x) · con (tmCon (list _) xs) ,  case-cons₁)

red-cons₂ : (M : X ⊢) → Maybe (∃ λ M' → CaseCons₂ R M M')
red-cons₂ M
 with (case? (con? (tmCon-list? (λ A → cons? ⋯ ⋯))) (⋯ ∷? ⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon-list! (cons! (match! x) (match! xs)))) (match! N₁ ∷! match! N₂ ∷! []!)) =
  just (N₁ · con (tmCon _ x) · con (tmCon (list _) xs) ,  case-cons₂)


red-nil : (M : X ⊢) → Maybe (∃ λ M' → CaseNil R M M')
red-nil M
  with (case? (con? (tmCon-list? (λ A → nil?))) (⋯ ∷? ⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon-list! nil!)) (match! N₁ ∷! match! N₂ ∷! []!)) = just (N₂ , case-nil)

red-pair : (M : X ⊢) → Maybe (∃ λ M' → CasePair R M M')
red-pair M
  with (case? (con? (tmCon-pair? λ A B → ⋯)) (⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon-pair! (match! (x ,, y)))) (match! N ∷! []!)) =
  just (N · con (tmCon _ x) · con (tmCon _ y) , case-pair)
```

Combining all reduction rules:

```
reduce : (M : X ⊢) → Maybe (∃ λ M' → Reduction R M M')
reduce =
  red-constr
  <|> red-unit
  <|> red-false₁
  <|> red-bool
  <|> red-integer
  <|> red-cons₁
  <|> red-cons₂
  <|> red-nil
  <|> red-pair
```

The pass is implemented as a bottom-up traversal that applies the reduction
rules:

```
reduceM : X ⊢ → Maybe (X ⊢)
reduceM = refine? (reduce {R = CaseReduce})

case-reduce : X ⊢ → X ⊢
case-reduce M = reduceM ↑? M
```

The computational translation relation:

```
Computational : Relation
Computational M M' = case-reduce M ≡ M'
```

### Deciding `Computational`

The computational relation admits a decision procedure:

```
decide : (M M' : X ⊢) → ProofOrCE (Computational M M')
decide M M' with case-reduce M ≟ M'
... | yes P = proof P
... | no ¬P  = ce ¬P caseReduceT M M'
```


## Soundness

The `case-reduce` function refines the `CaseReduce` relation:

```
variable
  M N : X ⊢

case-reduce-refines : CaseReduce M (case-reduce M)
case-reduce-refines = ↑?-refines CaseReduce cr-trans cr-TermCompat reduceM reduceM-CaseReduce
  where
    -- This helps with type inference
    red⊆cr : Reduction CaseReduce ⊆ CaseReduce
    red⊆cr = cr-reduction

    reduce-refine : Refines? reduceM (Reduction CaseReduce)
    reduce-refine = refine?-refines reduce

    reduceM-CaseReduce : Refines? reduceM CaseReduce
    reduceM-CaseReduce = Refines?-⊆ red⊆cr reduce-refine
```

The soundness lemma then follows from transitivity and reflexivity:

```
sound :
  ∀ {X} {M N : X ⊢}
  → Computational M N
  → CaseReduce M N
sound eq =
  cr-trans
    case-reduce-refines
    (cr-refl' eq)
```

Via soundness, we can define a checker that produces an inhabitant of the
equivalence.

```
check : (M M' : X ⊢) → Proof? (CaseReduce M M')
check M M' with case-reduce M ≟ M'
... | yes P = proof (sound P)
... | no _  = abort caseReduceT M M'
```



### Deciding `CaseReduce`

Interestingly, the inductive `CaseReduce` equivalence relation is decidable by
normalising both the pre- and post-term.

```
sound-both :
    case-reduce M ≡ case-reduce N
  → CaseReduce M N
sound-both eq =
  cr-trans
    case-reduce-refines
    (cr-trans
      (cr-refl' eq)
      (cr-sym case-reduce-refines)
    )

-- TODO: by induction on the `CaseReduce` derivation, requires a lemma for each
-- reduction rule
postulate
  complete-both : CaseReduce M N → case-reduce M ≡ case-reduce N
```

A decision procedure for that normalises both pre- and post-term. It is sound and
complete with respect to the inductive `CaseReduce` relation, but the
completeness proof is still to be done.

```
decide-CaseReduce : (M M' : X ⊢) → ProofOrCE (CaseReduce M M')
decide-CaseReduce M M' with case-reduce M ≟ case-reduce M'
... | yes P = proof (sound-both P)
... | no ¬P = ce (λ P → ¬P (complete-both P)) caseReduceT M M'
```
