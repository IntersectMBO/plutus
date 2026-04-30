{-# OPTIONS -v tc.instance:30 #-}
---
title: VerifiedCompilation.UCaseReduce
layout: page
---

# Case-Reduce Translation Phase

This module defines two translation relations for the case-reduce pass:

- `CaseReduce`: A "computational" relation that builds on a re-implementation
  of the compiler pass (`case-reduce` function below). The relation simply
  requires the reduced pre-term to be equal to the post-term. This was simpler
  than defining a decision procedure that compares pre- and post-term. The
  relation has a decision procedure.

- `_~_`: An inductive relation, built using the generic building blocks from
  `Untyped.Relation.Modular`. It is an equivalence relation which also admits a
  decision procedure which works by case-reducing _both_ the pre-term and
  post-term.

The `CaseReduce` relation is closer to the compiler implementation, while the
equivalence relation is more general and similar to the one in the "A Tale of
two Zippers" papers. The equivalence is more "obviously" semantics preserving.

The `CaseReduce` relation is sound (but not complete) w.r.t. the inductive
equivalence relation.

```
module VerifiedCompilation.UCaseReduce where

```
## Imports

```

open import Function using (_∘_)
open import Data.Bool using (true; false; if_then_else_; Bool)
open import Data.Maybe
open import Data.List using (List; _∷_; []; [_])
open import Data.Product
open import Data.Unit using (tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin using (Fin)
open import Data.Integer using (ℤ ; +_; -[1+_])

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Relation.Nullary using (yes; no; ¬_)

open import Untyped
open import Builtin.Constant.AtomicType
open import RawU using (tag2TyTag; tmCon; Tag)

open import Untyped.Equality
open import Untyped.Reduction using (iterApp)
open import Untyped.Relation.Binary
open import Untyped.Relation.Binary.Modular hiding (_<|>_)
open import Untyped.Transform
open Untyped.Transform.Refines?
open import Untyped.CEK using (lookup?)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; CaseReduceT; Proof?; abort)
open import VerifiedCompilation.UntypedViews
open import Utils using (_<|>_) renaming (_,_ to _,,_; _∷_ to cons; [] to nil)

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
  + Empty


private variable
  R : Relation
  X : ℕ

-- cr-constr : CaseConstr R ⊆ Reduction R
-- cr-constr = p0
-- 
-- cr-unit : CaseUnit R ⊆ Reduction R
-- cr-unit = p1
-- 
-- cr-false₁ : CaseFalse₁ R ⊆ Reduction R
-- cr-false₁ = p2
-- 
-- cr-bool : CaseBool R ⊆ Reduction R
-- cr-bool = p3
-- 
-- cr-integer : CaseInteger R ⊆ Reduction R
-- cr-integer = p4
-- 
-- cr-cons₁ : CaseCons₁ R ⊆ Reduction R
-- cr-cons₁ = p5
-- 
-- cr-cons₂ : CaseCons₂ R ⊆ Reduction R
-- cr-cons₂ = p6
-- 
-- cr-nil : CaseNil R ⊆ Reduction R
-- cr-nil = p7
-- 
-- cr-pair : CasePair R ⊆ Reduction R
-- cr-pair = p8
```

The equivalence is closed under the reduction rules and compatibility
rules

```
Rules : RelationT
Rules = Reduction + CompatTerm + Transitivity + Symmetry + Reflexivity + Empty

_~_ : Relation
_~_ = Fix Rules
```

Pattern synonyms for constructors:

```
cr-reduction : Reduction _~_ ⊆ _~_
cr-reduction p = fix (inl p)
pattern cr-compat p    = fix (inr (inl p))
pattern cr-trans p q   = fix (inr (inr (inl (transF p q))))
pattern cr-sym p       = fix (inr (inr (inr (inl (symF p)))))
pattern cr-refl        = fix (inr (inr (inr (inr (inl reflF)))))
```

Convenient helpers

```
cr-refl' :
  ∀ {X} {M N : X ⊢}
  → M ≡ N
  → M ~ N
cr-refl' refl = cr-refl

cr-refl* :
  ∀ {X} {Ms : List (X ⊢)}
  → Pointwise _~_ Ms Ms
cr-refl* = pointwise-refl {R = _~_} cr-refl

cr-TermCompat : TermCompatible _~_
cr-TermCompat = CompatTerm-TermCompatible (inj {G = Rules})
```

Testing the relation:

```
private module Test where
  M : 0 ⊢
  M = case (constr 0 []) (constr 0 [] ∷ constr 1 [] ∷ [])

  M' : 0 ⊢
  M' = constr 0 []

  MM' : M ~ M'
  MM' = cr-reduction (inl (case-constr refl))


  N : 0 ⊢
  N = case M (constr 42 [] ∷ [])
  N' : 0 ⊢
  N' = constr 42 []

  _ : N ~ N'
  _ =
    cr-trans
      (compat-case MM' cr-refl*)
      (cr-reduction (inl (case-constr refl)))
    where
      open TermCompatible cr-TermCompat
```

## CaseReduce translation relation

For each of the inductive reduction rules, we give a corresponding partial
function, which by construction is sound w.r.t `_~_`: it also produces proof of
the reduction rule when it succeeds (this comes in handy when proving soundness
w.r.t the inductive translation relation later on)

```
variable
  F : RelationT

red-constr : CaseConstr ≤ F → (M : X ⊢) → Maybe (∃ λ M' → Fix F M M')
red-constr inj M
  with (case? (constr? ⋯ ⋯) ⋯) M
... | no _ = nothing
... | yes (case! (constr! (match! i) (match! Ms)) (match! Ns))
  with lookup? i Ns in eq
... | nothing = nothing
... | just N = just (iterApp N Ms , fix (inj (case-constr eq)))

red-unit : CaseUnit ≤ F → (M : X ⊢) → Maybe (∃ λ M' → Fix F M M')
red-unit inj M
  with (case? (con? (tmCon? unit ⋯)) (⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon! (match! v))) (match! N ∷! []!))
  = just (N , fix (inj case-unit))

red-false₁ : CaseFalse₁ ≤ F → (M : X ⊢) → Maybe (∃ λ M' → Fix F M M')
red-false₁ inj M
  with (case? (con? (tmCon? bool (_≟_ false))) (⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon! refl)) (match! N ∷! []!))
  = just (N , fix (inj case-false₁))

red-bool : CaseBool ≤ F → (M : X ⊢) → Maybe (∃ λ M' → Fix F M M')
red-bool inj M
  with (case? (con? (tmCon? bool ⋯)) (⋯ ∷? ⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon! (match! b))) (match! N₁ ∷! match! N₂ ∷! []!))
    = just ((if b then N₂ else N₁) , fix (inj case-bool))

red-integer : CaseInteger ≤ F → (M : X ⊢) → Maybe (∃ λ M' → Fix F M M')
red-integer inj M
  with (case? (con? (tmCon? integer pos?)) ⋯) M
... | no _ = nothing
... | yes (case! (con! (tmCon! (pos! n))) (match! Ns))
  with lookup? n Ns in eq
... | nothing = nothing
... | just N = just (N , fix (inj (case-integer eq)))

red-cons₁ : CaseCons₁ ≤ F → (M : X ⊢) → Maybe (∃ λ M' → Fix F M M')
red-cons₁ inj M with
  (case? (con? (tmCon-list? (λ A xs → cons? ⋯ ⋯ xs))) (⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon-list! (cons! (match! x) (match! xs)))) (match! N ∷! []!)) =
  just (N · con (tmCon _ x) · con (tmCon (list _) xs) , fix (inj case-cons₁))

red-cons₂ : CaseCons₂ ≤ F → (M : X ⊢) → Maybe (∃ λ M' → Fix F M M')
red-cons₂ inj M
 with (case? (con? (tmCon-list? (λ A → cons? ⋯ ⋯))) (⋯ ∷? ⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon-list! (cons! (match! x) (match! xs)))) (match! N₁ ∷! match! N₂ ∷! []!)) =
  just (N₁ · con (tmCon _ x) · con (tmCon (list _) xs) , fix (inj case-cons₂))


red-nil : CaseNil ≤ F → (M : X ⊢) → Maybe (∃ λ M' → Fix F M M')
red-nil inj M
  with (case? (con? (tmCon-list? (λ A → nil?))) (⋯ ∷? ⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon-list! nil!)) (match! N₁ ∷! match! N₂ ∷! []!))
  = just (N₂ , fix (inj case-nil))

red-pair : CasePair ≤ F → (M : X ⊢) → Maybe (∃ λ M' → Fix F M M')
red-pair inj M
  with (case? (con? (tmCon-pair? λ A B → ⋯)) (⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon-pair! (match! (x ,, y)))) (match! N ∷! []!)) =
  just (N · con (tmCon _ x) · con (tmCon _ y) , fix (inj case-pair))
```

Combining all reduction rules gives a sound-by-construction reduction function:

```
test : Inj CasePair Reduction
test = Function.it

reduce : Reduction ≤ F → (M : X ⊢) → Maybe (∃ λ M' → Fix F M M')
reduce injF M =
  red-constr (injF ∘ inj {G = Reduction}) M
--  <|> red-unit (injF ∘ inj {G = Reduction}) M
--  <|> red-false₁ (injF ∘ inj {G = Reduction}) M
--  <|> red-bool (injF ∘ inj {G = Reduction}) M
--  <|> red-integer (injF ∘ inj {G = Reduction} ) M
--  <|> red-cons₁ (injF ∘ inj {G = Reduction}) M
--  <|> red-cons₂ (injF ∘ inj {G = Reduction}) M
--  <|> red-nil (injF ∘ inj {G = Reduction}) M
--  <|> red-pair (injF ∘ inj {G = Reduction}) M
```

### Alternative for sound-by-construction

We could alternatively set it up in a more extrinsic way:

```text
red-unit : X ⊢ → Maybe (X ⊢)

red-unit-sound : (M M' : X ⊢) → red-unit M ≡ just M' → CaseUnit R M M'
```

But this has to be done for each reduction rule and resulted in more boilerplate
code which disappears if you combine them.


## The pass

The pass is implemented as a bottom-up traversal that applies the reduction
rules:

```
reduceM : X ⊢ → Maybe (X ⊢)
reduceM = refine? (reduce {F = Rules} (inj {G = Rules}))

case-reduce : X ⊢ → X ⊢
case-reduce M = reduceM ↑? M

case-reduce* : List (X ⊢) → List (X ⊢)
case-reduce* Ms = reduceM ↑?* Ms
```

The computational translation relation:

```
CaseReduce : Relation
CaseReduce M M' = case-reduce M ≡ M'
```

### Deciding `CaseReduce`

The computational relation admits a decision procedure:

```
decide : (M M' : X ⊢) → ProofOrCE (CaseReduce M M')
decide M M' with case-reduce M ≟ M'
... | yes P = proof P
... | no ¬P  = ce ¬P CaseReduceT M M'
```


## Soundness

The `case-reduce` function refines the `_~_` relation:

```
case-reduce-refines : ∀ {M : X ⊢} → M ~ case-reduce M
case-reduce-refines = ↑?-refines _~_ cr-trans cr-TermCompat reduceM reduceM-~
  where
    -- This helps with type inference
    red⊆cr : Reduction _~_ ⊆ _~_
    red⊆cr = cr-reduction

    reduceM-~ : Refines? reduceM _~_
    reduceM-~ = refine?-refines (reduce {F = Rules} (inj {G = Rules}))
```

The soundness lemma then follows from transitivity and reflexivity:

```
sound :
  ∀ {X} {M N : X ⊢}
  → CaseReduce M N
  → M ~ N
sound eq =
  cr-trans
    case-reduce-refines
    (cr-refl' eq)
```

### Deciding `_~_`

Interestingly, `~` is decidable by case-reducing both the pre- and post-term.
This can be proven via soundness and completeness w.r.t:

```
_≈_ : Relation
M ≈ M' = case-reduce M ≡ case-reduce M'

_≈*_ : Relation*
_≈*_ = Pointwise _≈_
```

The decision procedure is currently not used, since it accepts unwanted compiler
behaviour, such as case-reducing in the opposite direction.

Completeness requires for each reduction rule in `_~_` a lemma that it is
admissible in `Computational`. Here is one proof for the `case-constr` rule.

```
module Decide
  {X : ℕ}
  -- TODO: completeness, by induction on the `_~_` derivation, requires a lemma for each
  -- reduction rule
  (complete-both : ∀ {M N : X ⊢} → M ~ N → case-reduce M ≡ case-reduce N)
  where

  sound-both :
    ∀ {X} {M N : X ⊢}
    → case-reduce M ≡ case-reduce N
    → M ~ N
  sound-both eq =
    cr-trans
      case-reduce-refines
      (cr-trans
        (cr-refl' eq)
        (cr-sym case-reduce-refines)
      )

  decide-~ : (M M' : X ⊢) → ProofOrCE (M ~ M')
  decide-~ M M' with case-reduce M ≟ case-reduce M'
  ... | yes P = proof (sound-both P)
  ... | no ¬P = ce (λ P → ¬P (complete-both P)) CaseReduceT M M'
```
