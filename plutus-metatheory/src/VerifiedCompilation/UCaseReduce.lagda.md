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

open import Function using (case_of_; _$_)
open import Data.Bool using (true; false; if_then_else_; Bool)
open import Data.Maybe
open import Data.Maybe.Properties using (just-injective)
open import Data.List using (List; _∷_; []; [_])
open import Data.Product
open import Data.Unit using (tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin using (Fin)
open import Data.Integer using (ℤ ; +_; -[1+_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_ ; _⊎-dec_)

open import Builtin.Constant.AtomicType
open import RawU using (tag2TyTag; tmCon; Tag)

open import Untyped
open import Untyped.Equality
open import Untyped.Reduction using (iterApp)
open import Untyped.Relation
open import Untyped.Relation.Composable
open import Untyped.Transform
open import Untyped.CEK using (lookup?)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; caseReduceT)
open import VerifiedCompilation.UntypedViews
open import Utils using () renaming (_,_ to _,,_; _∷_ to cons; [] to nil)

```
## Rules

These are the reduction rules of the case-reduce pass, defined as relation transformers.

```

module Rules where

  private variable
    X : ℕ
    M N N₁ N₂ : X ⊢
    Ns Ms : List (X ⊢)
    i : ℕ

  data CaseConstr (@++ R : Relation) : Relation where
    case-constr : ∀ {X} {i} {N : X ⊢} {Ns Ms} →
      lookup? i Ns ≡ just N →
      -------------------------------------------------
      CaseConstr R (case (constr i Ms) Ns) (iterApp N Ms)

  data CaseUnit (@++ R : Relation) : Relation where
    case-unit : ∀ {X} {N : X ⊢} →
       ---------------------------------------------
       CaseUnit R (case (con (tmCon unit tt)) [ N ]) N

  data CaseFalse₁ (@++ R : Relation) : Relation where
    case-false₁ : ∀ {X} {N : X ⊢} →
      --------------------------------------------------
      CaseFalse₁ R (case (con (tmCon bool false)) [ N ]) N

  data CaseBool (@++ R : Relation) : Relation where
    case-bool :
      ∀ {X} {b} {N₁ N₂ : X ⊢}  →
      -----------------------------------------------------------------------
      CaseBool R (case (con (tmCon bool b)) (N₁ ∷ N₂ ∷ [])) (if b then N₂ else N₁)

  data CaseInteger (@++ R : Relation) : Relation where
    case-integer :
      ∀ {X n} {N : X ⊢} {Ns} →
      lookup? n Ns ≡ just N →
      ---------------------------------------------------
      CaseInteger R (case (con (tmCon integer (+ n))) Ns) N

  data CaseCons₁ (@++ R : Relation) : Relation where
    case-cons₁ :
      ∀ {X} {A x xs} {N : X ⊢} →
      ----------------------------------------------------
      CaseCons₁ R
        (case (con (tmCon (list A) (cons x xs))) (N ∷ []))
        (N · con (tmCon A x) · con (tmCon (list A) xs))

  data CaseCons₂ (@++ R : Relation) : Relation where
    case-cons₂ :
      ∀ {X} {A x xs} {N₁ N₂ : X ⊢} →
      ----------------------------------------------------------
      CaseCons₂ R
        (case (con (tmCon (list A) (cons x xs))) (N₁ ∷ N₂ ∷ []))
        (N₁ · con (tmCon A x) · con (tmCon (list A) xs))

  data CaseNil (@++ R : Relation) : Relation where
    case-nil :
      ∀ {X} {N₁ N₂ : X ⊢} {A} →
      -----------------------------------------------------------
      CaseNil R
        (case (con (tmCon (list A) nil)) (N₁ ∷ N₂ ∷ []))
        N₂

  data CasePair (@++ R : Relation) : Relation where
    case-pair :
      ∀ {X} {A B x y} {N : X ⊢} →
      ----------------------------------------------------
      CasePair R
        (case (con (tmCon (pair A B) (x ,, y ))) (N ∷ []))
        (N · con (tmCon A x) · con (tmCon B y))

open Rules
```

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

cr-refl' : ∀ {X} {M N : X ⊢} → M ≡ N → CaseReduce M N
cr-refl' refl = cr-refl

-- TODO
postulate cr-refl* : ∀{X}{Ms : List (X ⊢)} → Pointwise CaseReduce Ms Ms
postulate cr-termcompat : TermCompatible CaseReduce

```

Testing the relation:

```
module Test where
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
      (cr-compat (compat-case MM' cr-refl*))
      (cr-reduction (inl (case-constr refl)))
```

## The reduction rules

```
private variable
  R : Relation

red-constr : Refinement? (CaseConstr CaseReduce)
red-constr M
  with (case? (constr? ⋯ ⋯) ⋯) M
... | no _ = nothing
... | yes (case! (constr! (match! i) (match! Ms)) (match! Ns))
  with lookup? i Ns in eq
... | nothing = nothing
... | just N = just (iterApp N Ms , case-constr eq)

red-unit : Refinement? (CaseUnit CaseReduce)
red-unit M
  with (case? (con? (tmCon? unit ⋯)) (⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon! (match! v))) (match! N ∷! []!))
  = just (N , case-unit)

red-false₁ : Refinement? (CaseFalse₁ CaseReduce)
red-false₁ M
  with (case? (con? (tmCon? bool (_≟_ false))) (⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon! refl)) (match! N ∷! []!)) = just (N , case-false₁)

red-bool : Refinement? (CaseBool CaseReduce)
red-bool M
  with (case? (con? (tmCon? bool ⋯)) (⋯ ∷? ⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon! (match! b))) (match! N₁ ∷! match! N₂ ∷! []!))
    = just ((if b then N₂ else N₁) , case-bool)

red-integer : Refinement? (CaseInteger CaseReduce)
red-integer M
  with (case? (con? (tmCon? integer pos?)) ⋯) M
... | no _ = nothing
... | yes (case! (con! (tmCon! (pos! n))) (match! Ns))
  with lookup? n Ns in eq
... | nothing = nothing
... | just N = just (N , case-integer eq)

red-cons₁ : Refinement? (CaseCons₁ CaseReduce)
red-cons₁ M with
  (case? (con? (tmCon-list? (λ A xs → cons? ⋯ ⋯ xs))) (⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon-list! (cons! (match! x) (match! xs)))) (match! N ∷! []!)) =
  just (N · con (tmCon _ x) · con (tmCon (list _) xs) ,  case-cons₁)

red-cons₂ : Refinement? (CaseCons₂ CaseReduce)
red-cons₂ M
 with (case? (con? (tmCon-list? (λ A → cons? ⋯ ⋯))) (⋯ ∷? ⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon-list! (cons! (match! x) (match! xs)))) (match! N₁ ∷! match! N₂ ∷! []!)) =
  just (N₁ · con (tmCon _ x) · con (tmCon (list _) xs) ,  case-cons₂)


red-nil : Refinement? (CaseNil CaseReduce)
red-nil M
  with (case? (con? (tmCon-list? (λ A → nil?))) (⋯ ∷? ⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon-list! nil!)) (match! N₁ ∷! match! N₂ ∷! []!)) = just (N₂ , case-nil)

red-pair : Refinement? (CasePair CaseReduce)
red-pair M
  with (case? (con? (tmCon-pair? λ A B → ⋯)) (⋯ ∷? []?)) M
... | no _ = nothing
... | yes (case! (con! (tmCon-pair! (match! (x ,, y)))) (match! N ∷! []!)) =
  just (N · con (tmCon _ x) · con (tmCon _ y) , case-pair)

reduce : Refinement? (Reduction CaseReduce)
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

reduceM : ∀ {X} → X ⊢ → Maybe (X ⊢)
reduceM = run? reduce

norm : ∀ {X} → X ⊢ → X ⊢
norm M = reduceM ↑? M

reduceM-CaseReduce : Refines? reduceM CaseReduce
reduceM-CaseReduce = Refines?-⊆ red⊆cr (run?-refines reduce)
  where
    -- This helps with inference
    red⊆cr : Reduction CaseReduce ⊆ CaseReduce
    red⊆cr = cr-reduction


norm-CaseReduce : Refines norm CaseReduce
norm-CaseReduce = ↑?-relating
  where open Refines? CaseReduce cr-trans cr-termcompat reduceM reduceM-CaseReduce

norm* : ∀ {X} → List (X ⊢) → List (X ⊢)
norm* Ns = run? reduce ↑?* Ns

```

## Soundness

```
sound-norm-norm : ∀ {X} {M N : X ⊢} → norm M ≡ norm N → CaseReduce M N
sound-norm-norm eq =
  cr-trans
    norm-CaseReduce
    (cr-trans
      (cr-refl' eq)
      (cr-sym norm-CaseReduce)
    )

sound-norm : ∀ {X} {M N : X ⊢} → norm M ≡ N → CaseReduce M N
sound-norm eq =
  cr-trans
    norm-CaseReduce
    (cr-refl' eq)
```


## Checker and Decision procedure

The checker normalises the pre-term and uses the soundness proof:

```
check :  ∀ {X} (M M' : X ⊢) → Maybe (CaseReduce M M')
check M M' with norm M ≟ M'
... | yes P = just (sound-norm P)
... | no ¬P = nothing
```

A decision procedure that normalises both pre- and post-term. It is sound and
complete with respect to the inductive `CaseReduce` relation, but the
completeness proof is still to be done.

```
decide : ∀ {X} (M M' : X ⊢) → ProofOrCE (norm M ≡ norm M')
decide M M' with norm M ≟ norm M'
... | yes P = proof P
... | no ¬P = ce ¬P caseReduceT M M'
```
