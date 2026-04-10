---
title: VerifiedCompilation.UCaseReduce
layout: page
---

# Case-Reduce Translation Phase
```
{-# OPTIONS --polarity #-}
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
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

-- todo, these should be re-exported from Untyped
-- open import Builtin.Constant.AtomicType
-- open import Builtin.Signature as B using (_⊢♯)
-- open _⊢♯

-- open import Untyped.Equality using (DecEq; _≟_;decPointwise)
-- open import VerifiedCompilation.UntypedViews
-- open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation; convert; reflexive; TransMatch)
-- open import Relation.Nullary using (_×-dec_)
-- open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error; con-integer)
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl)
-- open import Relation.Binary.PropositionalEquality.Core using (trans; sym; cong; cong₂; subst)
-- open import Untyped.CEK using (lookup?; lookup?-deterministic)
-- open import Data.Fin using (Fin; zero; suc)
-- open import Data.Nat using (ℕ; zero; suc)
-- open import Data.List using (List; _∷_; []; [_]; map)
-- open import Data.Maybe using (Maybe; just; nothing)
-- open import Data.Bool hiding (_≟_)
-- open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
-- open import Data.Integer using (ℤ ; +_)
-- import Relation.Binary as Binary using (Decidable)
-- open import Relation.Nullary using (Dec; yes; no; ¬_)
-- open import Data.Product using (_,_)
-- open import RawU using (tag2TyTag; tmCon; Tag)
-- open Tag
-- open import Agda.Builtin.Int using (Int)
-- open import Data.Empty using (⊥)
-- open import Function using (case_of_; _$_)
-- open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; caseReduceT)
-- open import Untyped.Reduction using (iterApp)
-- open import Builtin
-- open import VerifiedCompilation.Trace using (caseReduceT)
-- open import Untyped.Transform
-- open import Untyped.Relation
-- 
-- import Relation.Binary.Reasoning.Setoid as Reasoning
```



## Rules

Reduction rules of case-of-constr


```

private variable
  X : ℕ

module Rules where

  private variable
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


```
ReductionF : RelF
ReductionF
  = CaseConstr
  + CaseUnit
  + CaseFalse₁
  + CaseBool
  + CaseInteger
  + CaseCons₁
  + CaseCons₂
  + CaseNil
  + CasePair

CaseReduce : Relation
CaseReduce = Mu (CompatTerm + ReductionF + Transitivity + Symmetry + Reflexivity)


pattern cr-compat p    = fix (inl p)
pattern cr-reduction p = fix (inr (inl p))
pattern cr-trans p q   = fix (inr (inr (inl (transF p q))))
pattern cr-sym p       = fix (inr (inr (inr (inl (symF p)))))
pattern cr-refl        = fix (inr (inr (inr (inr reflF))))

≡-cr : ∀ {X}{M N : X ⊢} → M ≡ N → CaseReduce M N
≡-cr refl = cr-refl

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

## Running reduction rules

Partial

```
Run? : RelF → Relation → Set
Run? F R = ∀ {X} → (M : X ⊢) → Dec (∃ (F R M))

run? : ∀ {F : RelF} {R : Relation} → Run? F R → X ⊢ → Maybe (X ⊢)
run? f M with f M
... | no _ = nothing
... | yes (M' , _) = just M'

run?-rel : ∀ {F : RelF} {R : Relation} → (f : Run? F R) →
  Extensive? (run? {_} {F} {R} f) (F R)
run?-rel f {_} M eq with f M | eq
... | yes (_ , RMN) | refl = RMN

infixr 5 _<|>_
_<|>_ : ∀ {R S : RelF} {T : Relation} → Run? R T → Run? S T → Run? (R + S) T
(f <|> g) M with f M
... | yes (N , RMN) = yes (N , inl RMN)
... | no ¬RMN with g M
... | yes (N , SMN) = yes (N , inr SMN)
... | no ¬SMN = no λ { (_ , inl RMN) → ¬RMN (_ , RMN) ; (_ , inr SMN) → ¬SMN (_ , SMN)}
```

## The reduction rules

```
private variable
  R : Relation

red-constr : Run? CaseConstr CaseReduce
red-constr M
  with (case? (constr? ⋯ ⋯) ⋯) M
... | no ¬P = no λ { (_ , case-constr _) →  ¬P inhabitant}
... | yes (case! (constr! (match! i) (match! Ms)) (match! Ns))
  with lookup? i Ns in eq
... | nothing = no λ { (M' , case-constr eq') → case (trans (sym eq) eq') of λ ()}
... | just N = yes (iterApp N Ms , case-constr eq)

red-unit : Run? CaseUnit CaseReduce
red-unit M
  with (case? (con? (tmCon? unit ⋯)) (⋯ ∷? []?)) M
... | no ¬P = no λ {(_ , case-unit) → ¬P inhabitant}
... | yes (case! (con! (tmCon! (match! v))) (match! N ∷! []!))
  = yes (N , case-unit)

red-false₁ : Run? CaseFalse₁ CaseReduce
red-false₁ M
  with (case? (con? (tmCon? bool (_≟_ false))) (⋯ ∷? []?)) M
... | no ¬P = no λ {(_ , case-false₁) → ¬P inhabitant}
... | yes (case! (con! (tmCon! refl)) (match! N ∷! []!)) = yes (N , case-false₁)

red-bool : Run? CaseBool CaseReduce
red-bool M
  with (case? (con? (tmCon? bool ⋯)) (⋯ ∷? ⋯ ∷? []?)) M
... | no ¬P = no λ {(_ , case-bool) → ¬P inhabitant}
... | yes (case! (con! (tmCon! (match! b))) (match! N₁ ∷! match! N₂ ∷! []!))
    = yes ((if b then N₂ else N₁) , case-bool)

red-integer : Run? CaseInteger CaseReduce
red-integer M
  with (case? (con? (tmCon? integer pos?)) ⋯) M
... | no ¬P = no λ {(_ , case-integer _) → ¬P inhabitant}
... | yes (case! (con! (tmCon! (pos! n))) (match! Ns))
  with lookup? n Ns in eq
... | nothing = no λ {(_ , case-integer eq') → case trans (sym eq) eq' of λ ()}
... | just N = yes (N , case-integer eq)

red-cons₁ : Run? CaseCons₁ CaseReduce
red-cons₁ M with
  (case? (con? (tmCon-list? (λ A xs → cons? ⋯ ⋯ xs))) (⋯ ∷? []?)) M
... | no ¬P = no λ {(_ , case-cons₁) → ¬P inhabitant}
... | yes (case! (con! (tmCon-list! (cons! (match! x) (match! xs)))) (match! N ∷! []!)) =
  yes (N · con (tmCon _ x) · con (tmCon (list _) xs) ,  case-cons₁)

red-cons₂ : Run? CaseCons₂ CaseReduce
red-cons₂ M
 with (case? (con? (tmCon-list? (λ A → cons? ⋯ ⋯))) (⋯ ∷? ⋯ ∷? []?)) M
... | no ¬P = no λ {(_ , case-cons₂) → ¬P inhabitant}
... | yes (case! (con! (tmCon-list! (cons! (match! x) (match! xs)))) (match! N₁ ∷! match! N₂ ∷! []!)) =
  yes (N₁ · con (tmCon _ x) · con (tmCon (list _) xs) ,  case-cons₂)


red-nil : Run? CaseNil CaseReduce
red-nil M
  with (case? (con? (tmCon-list? (λ A → nil?))) (⋯ ∷? ⋯ ∷? []?)) M
... | no ¬P = no λ {(_ , case-nil) → ¬P inhabitant}
... | yes (case! (con! (tmCon-list! nil!)) (match! N₁ ∷! match! N₂ ∷! []!)) = yes (N₂ , case-nil)

red-pair : Run? CasePair CaseReduce
red-pair M
  with (case? (con? (tmCon-pair? λ A B → ⋯)) (⋯ ∷? []?)) M
... | no ¬P = no λ {(_ , case-pair) → ¬P inhabitant}
... | yes (case! (con! (tmCon-pair! (match! (x ,, y)))) (match! N ∷! []!)) =
  yes (N · con (tmCon _ x) · con (tmCon _ y) , case-pair)

reduce : Run? ReductionF CaseReduce
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

reduceM : X ⊢ → Maybe (X ⊢)
reduceM = run? {_} {ReductionF} {CaseReduce} reduce

norm : ∀ {X} → X ⊢ → X ⊢
norm M = reduceM ⇑ M

reduceM-ext : Extensive? reduceM (ReductionF CaseReduce)
reduceM-ext = run?-rel reduce

-- This helps with inference
red⊆cr : ReductionF CaseReduce ⊆ CaseReduce
red⊆cr = cr-reduction

reduceM-ext' : Extensive? reduceM CaseReduce
reduceM-ext' = ext?-⊆ red⊆cr reduceM-ext

norm-ext : Extensive norm CaseReduce
norm-ext = ⇑-extensive
  where open Extensive? CaseReduce cr-trans cr-termcompat reduceM reduceM-ext'

norm* : ∀ {X} → List (X ⊢) → List (X ⊢)
norm* Ns = run? {_} {ReductionF} {CaseReduce} reduce ⇑* Ns

```

## Soundness

```
sound : ∀ {X} {M N : X ⊢} → norm M ≡ norm N → CaseReduce M N
sound eq =
  cr-trans
    norm-ext
    (cr-trans
      (≡-cr eq)
      (cr-sym norm-ext)
    )

```


## Decision procedure

The decision procedure is straightforward:

```
decide : ∀ {X} (M M' : X ⊢) → ProofOrCE (norm M ≡ norm M')
decide M M' with norm M ≟ norm M'
... | yes P = proof P
... | no ¬P = ce ¬P caseReduceT M M'
```

-- infixr 5 _+_
-- _+_ : Relation → Relation → Relation
-- (R + S) X Y = R X Y ⊎ S X Y
-- 
-- infixr 5 _Else_
-- _Else_ : Relation → Relation → Relation
-- (R Else S) X Y = R X Y ⊎ (¬ R X Y × S X Y) -- TODO: de Morgan's law?
-- 
-- Reduction : Relation
-- Reduction =
--   CaseConstr
--   + CaseUnit
--   + CaseFalse₁
--   + CaseBool
--   + CaseInteger
--   + CaseCons₁
--   + CaseCons₂
--   + CaseNil
--   + CasePair
-- 
-- Run? : Relation → Set
-- Run? R = ∀ {X} → (M : X ⊢) → Dec (∃ (R M))
-- 
-- PFunc : Relation → Set
-- PFunc R = ∀ {X} → (M : X ⊢) → Dec (∃! _≡_ (λ N → R M N))
-- 
-- Func : Relation → Set
-- Func R = ∀ {X} → (M : X ⊢) → ∃! _≡_ (λ N → R M N)
-- 
-- Run : Relation → Set
-- Run R = ∀ {X} → (M : X ⊢) → Σ (X ⊢) (R M)
-- 
-- 
-- Reduction' : Relation
-- Reduction' =
--   CaseConstr
--   Else CaseUnit
--   Else CaseFalse₁
--   Else CaseBool
--   Else CaseInteger
--   Else CaseCons₁
--   Else CaseCons₂
--   Else CaseNil
--   Else CasePair
-- 
-- infixr 5 _else_
-- _else_ : ∀ {R S : Relation} → Run? R → Run? S → Run? (R Else S)
-- (f else g) M with f M
-- ... | yes (N , RMN) = yes (N , inj₁ RMN)
-- ... | no ¬∃RM with g M
-- ... | yes (N , SMN) = yes (N , inj₂ ((λ RMN → ¬∃RM ( _ , RMN )) , SMN))
-- ... | no ¬SMN = no λ { (_ , inj₁ RMN) → ¬∃RM (_ , RMN)
--                      ; (_ , inj₂ (_ , SMN)) → ¬SMN (_ , SMN)}
-- 
-- Deterministic : Relation → Set
-- Deterministic R = ∀ {X} {M N N' : X ⊢} → R M N → R M N' → N ≡ N'
-- 
-- 
-- -- I don't think this holds
-- -- det-else : ∀ {R S : Relation} → Deterministic R → Deterministic S → Deterministic (R Else S)
-- -- det-else det-R det-S (inj₁ RMN) (inj₁ RMN') = det-R RMN RMN'
-- -- det-else det-R det-S (inj₂ (_ , SMN)) (inj₂ (_ , SMN')) = det-S SMN SMN'
-- -- det-else det-R det-S (inj₁ RMN) (inj₂ (¬RMN' , _)) = ?
-- -- det-else det-R det-S (inj₂ (¬RMN , _)) (inj₁ RMN') = ?
-- 
-- det-constr : Deterministic CaseConstr
-- det-constr (case-constr lookup≡) (case-constr lookup≡')
--   rewrite (just-injective (trans (sym lookup≡) lookup≡')) = refl
-- 
-- det-unit : Deterministic CaseUnit
-- det-unit case-unit case-unit = refl
-- 
-- det-false₁ : Deterministic CaseFalse₁
-- det-false₁ case-false₁ case-false₁ = refl
-- 
-- det-bool : Deterministic CaseBool
-- det-bool case-bool case-bool = refl
-- 
-- det-integer : Deterministic CaseInteger
-- det-integer (case-integer lookup≡) (case-integer lookup≡')
--   rewrite (just-injective (trans (sym lookup≡) lookup≡')) = refl
-- 
-- det-cons₁ : Deterministic CaseCons₁
-- det-cons₁ case-cons₁ case-cons₁ = refl
-- 
-- det-cons₂ : Deterministic CaseCons₂
-- det-cons₂ case-cons₂ case-cons₂ = refl
-- 
-- det-nil : Deterministic CaseNil
-- det-nil case-nil case-nil = refl
-- 
-- det-pair : Deterministic CasePair
-- det-pair case-pair case-pair = refl
-- ```
-- 
-- ```
-- infixr 5 _<|>_
-- _<|>_ : ∀ {R S : Relation} → Run? R → Run? S → Run? (R + S)
-- (f <|> g) M with f M
-- ... | yes (N , RMN) = yes (N , inj₁ RMN)
-- ... | no ¬RMN with g M
-- ... | yes (N , SMN) = yes (N , inj₂ SMN)
-- ... | no ¬SMN = no λ { (_ , inj₁ RMN) → ¬RMN (_ , RMN) ; (_ , inj₂ SMN) → ¬SMN (_ , SMN)}
-- 
-- 
-- id : {R : Relation} → Reflexive R → Run R
-- id R-refl _ = (_ , R-refl)
-- 
-- 
-- _∘_ : {R : Relation} → Transitive R → Run R → Run R → Run R
-- _∘_ R-trans f g M with f M
-- ... | (N , R₁) with g N
-- ... | (L , R₂) = (L , R-trans R₁ R₂)
-- 
-- infixr 5 _?<|>_
-- _?<|>_ : {R S : Relation} → Run? R → Run S → Run (R + S)
-- _?<|>_ f? g M with f? M
-- ... | yes (N , P) = (N , inj₁ P)
-- ... | no _ with g M
-- ... | (N , P) = (N , inj₂ P)
-- 
-- run-refl : Run Reflexivity
-- run-refl M = (M , ~-refl)
-- 
-- red-constr : Run? CaseConstr
-- red-constr M
--   with (case? (constr? ⋯ ⋯) ⋯) M
-- ... | no ¬P = no λ { (_ , case-constr _) →  ¬P inhabitant}
-- ... | yes (case! (constr! (match! i) (match! Ms)) (match! Ns))
--   with lookup? i Ns in eq
-- ... | nothing = no λ { (M' , case-constr eq') → case (trans (sym eq) eq') of λ ()}
-- ... | just N = yes (iterApp N Ms , case-constr eq)
-- 
-- -- ⌞_⌟ : Run? → ∀{X} → X ⊢ → Maybe (X ⊢)
-- -- ⌞ f ⌟ M with f M
-- -- ... | yes (N , _) = just N
-- -- ... | no _ = nothing
-- 
-- -- complete-constr : ∀ {M N} → CaseConstr M N → red-constr M ≡ N
-- -- complete-constr = ?
-- 
-- red-unit-M : ∀ {X} → X ⊢ → Maybe (X ⊢)
-- red-unit-M M
--   with (case? (con? (tmCon? unit ⋯)) (⋯ ∷? []?)) M
-- ... | no _ = nothing
-- ... | yes (case! (con! (tmCon! (match! v))) (match! N ∷! []!))
--   = just N
-- 
-- red-unit-M-sound : ∀ {X} (M N : X ⊢) → red-unit-M M ≡ just N → CaseUnit M N
-- red-unit-M-sound M N
--   with (case? (con? (tmCon? unit ⋯)) (⋯ ∷? []?)) M
-- ... | no ¬P = {! !} -- no λ {(_ , case-unit) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon! (match! v))) (match! N ∷! []!))
--   = {! !}
--   -- = yes (N , case-unit)
-- 
-- red-unit : Run? CaseUnit
-- red-unit M
--   with (case? (con? (tmCon? unit ⋯)) (⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-unit) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon! (match! v))) (match! N ∷! []!))
--   = yes (N , case-unit)
-- 
-- red-false₁ : Run? CaseFalse₁
-- red-false₁ M
--   with (case? (con? (tmCon? bool (_≟_ false))) (⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-false₁) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon! refl)) (match! N ∷! []!)) = yes (N , case-false₁)
-- 
-- red-bool : Run? CaseBool
-- red-bool M
--   with (case? (con? (tmCon? bool ⋯)) (⋯ ∷? ⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-bool) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon! (match! b))) (match! N₁ ∷! match! N₂ ∷! []!))
--     = yes ((if b then N₂ else N₁) , case-bool)
-- 
-- red-integer : Run? CaseInteger
-- red-integer M
--   with (case? (con? (tmCon? integer pos?)) ⋯) M
-- ... | no ¬P = no λ {(_ , case-integer _) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon! (pos! n))) (match! Ns))
--   with lookup? n Ns in eq
-- ... | nothing = no λ {(_ , case-integer eq') → case trans (sym eq) eq' of λ ()}
-- ... | just N = yes (N , case-integer eq)
-- 
-- red-cons₁ : Run? CaseCons₁
-- red-cons₁ M with
--   (case? (con? (tmCon-list? (λ A xs → cons? ⋯ ⋯ xs))) (⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-cons₁) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon-list! (cons! (match! x) (match! xs)))) (match! N ∷! []!)) =
--   yes (N · con (tmCon _ x) · con (tmCon (list _) xs) ,  case-cons₁)
-- 
-- red-cons₂ : Run? CaseCons₂
-- red-cons₂ M
--  with (case? (con? (tmCon-list? (λ A → cons? ⋯ ⋯))) (⋯ ∷? ⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-cons₂) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon-list! (cons! (match! x) (match! xs)))) (match! N₁ ∷! match! N₂ ∷! []!)) =
--   yes (N₁ · con (tmCon _ x) · con (tmCon (list _) xs) ,  case-cons₂)
-- 
-- 
-- red-nil : Run? CaseNil
-- red-nil M
--   with (case? (con? (tmCon-list? (λ A → nil?))) (⋯ ∷? ⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-nil) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon-list! nil!)) (match! N₁ ∷! match! N₂ ∷! []!)) = yes (N₂ , case-nil)
-- 
-- red-pair : Run? CasePair
-- red-pair M
--   with (case? (con? (tmCon-pair? λ A B → ⋯)) (⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-pair) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon-pair! (match! (x ,, y)))) (match! N ∷! []!)) =
--   yes (N · con (tmCon _ x) · con (tmCon _ y) , case-pair)
-- 
-- run?-Maybe : ∀ {P : Relation} → Run? (P) → X ⊢ → Maybe (X ⊢)
-- run?-Maybe step M with step M
-- ... | no _ = nothing
-- ... | yes (M' , _) = just M'
-- 
-- run : ∀ {R : Relation} → Run R → X ⊢ → X ⊢
-- run f x with f x
-- ... | (N , _) = N
-- 
-- 
-- 
-- infixr 5 _||_
-- _||_ : ∀ {R S : Relation}
--  → Run? R
--  → Run? S
--  → Run? (R + S)
-- (stepR || stepS) M
--   with stepR M
-- ... | yes (M' , R) = yes (M' , inj₁ R)
-- ... | no ¬R
--   with stepS M
-- ... | yes (M' , S) = yes (M' , inj₂ S)
-- ... | no ¬S = no λ { (M' , inj₁ R) → ¬R (M' , R)
--                    ; (M' , inj₂ S) → ¬S (M' , S)}
-- 
-- reduce : Run? Reduction
-- reduce =
--   red-constr
--   <|> red-unit
--   <|> red-false₁
--   <|> red-bool
--   <|> red-integer
--   <|> red-cons₁
--   <|> red-cons₂
--   <|> red-nil
--   <|> red-pair
-- 
-- reduce' : Run? Reduction'
-- reduce' =
--   red-constr
--   else red-unit
--   else red-false₁
--   else red-bool
--   else red-integer
--   else red-cons₁
--   else red-cons₂
--   else red-nil
--   else red-pair
-- 
-- reduceM : ∀ {X} → X ⊢ → Maybe (X ⊢)
-- reduceM = run?-Maybe reduce
-- 
-- Test = Reduction + Reflexivity -- todo transitivity/compatibility
-- 
-- test : Run Test
-- test = reduce ?<|> run-refl
-- 
-- norm' : ∀ {X} → X ⊢ → X ⊢
-- norm' M = reduceM ⇑ M
-- 
-- norm'* : ∀ {X} → List (X ⊢) → List (X ⊢)
-- norm'* Ns = reduceM ⇑* Ns
-- ```
-- 
-- ## Relation
-- 
-- ```
-- 
-- private variable
--   L M N M' N' : X ⊢
--   Ns Ms Ms' Ns' : List (X ⊢)
--   i : ℕ
-- 
-- -- infix 3 _~_
-- 
-- -- data _~_ {X : ℕ} : X ⊢ → X ⊢ → Set where
-- -- 
-- --   reduction :
-- --      Reduction M M' →
-- --      --------------
-- --      M ~ M'
-- -- 
-- --   ~-refl :
-- --     ----------
-- --     M ~ M
-- -- 
-- --  ~-trans :
-- --    L ~ M →
-- --    M ~ N →
-- --    -----
-- --    L ~ N
-- --
-- --  ~-var : ∀ {x : Fin X} →
-- --    ---------
-- --    ` x ~ ` x
-- --
-- --  ~-lam :
-- --    M ~ M' →
-- --    -----------
-- --    ƛ M ~ ƛ M'
-- --
-- --  ~-app :
-- --    M ~ M' →
-- --    N ~ N' →
-- --    -----------------
-- --    M · N ~ M' · N'
-- --
-- --  ~-force :
-- --    M ~ M' →
-- --    ------------
-- --    force M ~ force M'
-- --
-- --  ~-delay :
-- --    M ~ M' →
-- --    ------------
-- --    delay M ~ delay M'
-- --
-- --  ~-constr :
-- --    Pointwise _~_ Ms Ms' →
-- --    --------------------
-- --    constr i Ms ~ constr i Ms'
-- --
-- --  ~-case :
-- --    M ~ M' →
-- --    Pointwise _~_ Ms Ms' →
-- --    --------------------
-- --    case M Ms ~ case M' Ms'
-- --
-- --  ~-con : ∀ {K} →
-- --    ---------
-- --    con K  ~ con K
-- --
-- --  ~-builtin : ∀ {b} →
-- --    ---------------------
-- --    builtin b ~ builtin b
-- --
-- --  ~-error :
-- --    ---------------------
-- --    error ~ error
-- ```
-- 
-- ## Extensivity
-- 
-- ```
-- is-yes : ∀{A : Set} → Dec A → Bool
-- is-yes (yes _) = true
-- is-yes (no _) = false
-- 
-- run-fun : ∀ {R : Relation} → Run R → X ⊢ → X ⊢
-- run-fun f M with f M
-- ... | N , _ = N
-- 
-- run-extensive : ∀ {R : Relation} → (f : Run R) → Extensive (run-fun f) R
-- run-extensive f {_} {M} with f M
-- ... | _ , RMN = RMN
-- 
-- module Test
--   (R : Relation)
--   (R-sym : Symmetric R)
--   (R-refl : Reflexive R)
--   (R-trans : Transitive R) -- todo for 
--   (f : ∀ {X} → X ⊢ → X ⊢)
--   (f-extensive : Extensive f R)
--   where
-- 
--   Computational : Relation
--   Computational M N = f M ≡ f N
-- 
--   R-refl' : ∀ {X} {M N : X ⊢} → M ≡ N → R M N
--   R-refl' refl = R-refl
-- 
--   sound : ∀{X} {M N : X ⊢} → Computational M N → R M N
--   sound {_} {M} {N} fM≡fN = R-trans (R-trans (f-extensive {M = M}) (R-refl' fM≡fN)) (R-sym (f-extensive {M = N}))
-- 
-- postulate
--   sound : ∀ {X} {M N : X ⊢} → run-fun test M ≡ N → Test M N
--   -- similar to above
-- 
-- postulate Test-idempotent : Idempotent Test
-- 
-- postulate Test-trans : Transitive Test
-- -- by idempotence
-- 
-- postulate Test-refl : Reflexive Test
-- -- by compatibility rules
-- 
-- -- Does not hold because normalising on one side does not admit the
-- -- compatibility rule for case
-- -- complete : ∀ {X} {M N : X ⊢} → Test M N → run-fun test M ≡ N
-- -- 
-- -- complete = ? -- TODO: +-like combinator that combines all cases (let's hope it doesn't need TERMINATING), otherwise pattern synonyms
-- 
-- dec-test : ∀ {R : Relation} → Func R → ∀ (M N : X ⊢) → Dec (R M N)
-- dec-test f M N with f M
-- ... | M' , M~M' , unique with M' ≟ N
-- ... | yes refl = yes M~M'
-- ... | no ¬M≡M' = no (λ RMN → ¬M≡M' (unique RMN))
-- 
-- -- dec-test2 : ∀ {R : Relation}
-- --   → Transitive R
-- --   → Reflexive R
-- --   → Run R
-- --   → ∀ (M N : X ⊢)
-- --   → Dec (R M N)
-- -- dec-test2 R-trans R-refl f M N with f M
-- -- ... | M' , M~M' with M' ≟ N
-- -- ... | yes refl = yes M~M'
-- -- ... | no ¬M≡M = no λ RMN → {! !}
-- 
-- 
-- -- reduce-~ : ∀ {M M' : X ⊢} → is-yes (test M) → M ~ N'
-- -- reduce-~ {_} {M} {M'} refl = ?
-- 
-- --norm-extensive : M ~ norm M
-- --norm-extensive = ↑-extensive
-- --  where open Extensive _~_ ~-trans ~-compat reduce reduce-~
-- ```
-- 
-- 
-- ```
-- -- case-constr? : ∀ (M M' : X ⊢) → red-constr M ≡ just M' → CaseConstr M M'
-- -- case-constr? M _
-- --   with (case? (constr? ⋯ ⋯) ⋯) M
-- -- ... | no _ = λ ()
-- -- ... | yes (case! (constr! (match! i) (match! Ms)) (match! Ns))
-- --   with lookup? i Ms in eq
-- -- ... | nothing = λ ()
-- -- ... | just N = λ _ → case-constr eq
-- ```
-- 
-- 
-- ## Relation
-- 
-- The relation simply states that the terms are (syntactically) equal after
-- normalising the pre-term:
-- 
-- ```
-- _≡-c'_ : Relation
-- M ≡-c' N = norm' M ≡ N
-- ```
-- 
-- ## Decision procedure
-- 
-- The decision procedure is straightforward:
-- 
-- ```
-- decide' : ∀ {X} (M M' : X ⊢) → ProofOrCE (M ≡-c' M')
-- decide' M M' with norm' M ≟ M'
-- ... | yes P = proof P
-- ... | no ¬P = ce ¬P caseReduceT M M'
-- ```
-- 
-- 
-- The following are unused results:
-- 
-- ```
-- pfunc-constr : PFunc CaseConstr
-- pfunc-constr M
--   with (case? (constr? ⋯ ⋯) ⋯) M
-- ... | no ¬P = no λ { (_ , case-constr _ , _) →  ¬P inhabitant}
-- ... | yes (case! (constr! (match! i) (match! Ms)) (match! Ns))
--   with lookup? i Ns in eq
-- ... | nothing = no λ { (M' , case-constr eq' , _) → case (trans (sym eq) eq') of λ ()}
-- ... | just N = yes (iterApp N Ms , case-constr eq , det-constr (case-constr eq))
-- 
-- pfunc-unit : PFunc CaseUnit
-- pfunc-unit M
--   with (case? (con? (tmCon? unit ⋯)) (⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-unit , _) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon! (match! v))) (match! N ∷! []!))
--   = yes (N , case-unit , det-unit case-unit)
-- 
-- pfunc-false₁ : PFunc CaseFalse₁
-- pfunc-false₁ M
--   with (case? (con? (tmCon? bool (_≟_ false))) (⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-false₁ , _) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon! refl)) (match! N ∷! []!)) = yes (N , case-false₁ , det-false₁ case-false₁)
-- 
-- pfunc-bool : PFunc CaseBool
-- pfunc-bool M
--   with (case? (con? (tmCon? bool ⋯)) (⋯ ∷? ⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-bool , _) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon! (match! b))) (match! N₁ ∷! match! N₂ ∷! []!))
--     = yes ((if b then N₂ else N₁) , case-bool , det-bool case-bool)
-- 
-- pfunc-integer : PFunc CaseInteger
-- pfunc-integer M
--   with (case? (con? (tmCon? integer pos?)) ⋯) M
-- ... | no ¬P = no λ {(_ , case-integer _ , _) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon! (pos! n))) (match! Ns))
--   with lookup? n Ns in eq
-- ... | nothing = no λ {(_ , case-integer eq' , _) → case trans (sym eq) eq' of λ ()}
-- ... | just N = yes (N , case-integer eq , det-integer (case-integer eq))
-- 
-- pfunc-cons₁ : PFunc CaseCons₁
-- pfunc-cons₁ M with
--   (case? (con? (tmCon-list? (λ A xs → cons? ⋯ ⋯ xs))) (⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-cons₁ , _) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon-list! (cons! (match! x) (match! xs)))) (match! N ∷! []!)) =
--   yes (N · con (tmCon _ x) · con (tmCon (list _) xs) , case-cons₁ , det-cons₁ case-cons₁)
-- 
-- pfunc-cons₂ : PFunc CaseCons₂
-- pfunc-cons₂ M
--  with (case? (con? (tmCon-list? (λ A → cons? ⋯ ⋯))) (⋯ ∷? ⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-cons₂ , _) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon-list! (cons! (match! x) (match! xs)))) (match! N₁ ∷! match! N₂ ∷! []!)) =
--   yes (N₁ · con (tmCon _ x) · con (tmCon (list _) xs) ,  case-cons₂ , det-cons₂ case-cons₂)
-- 
-- 
-- pfunc-nil : PFunc CaseNil
-- pfunc-nil M
--   with (case? (con? (tmCon-list? (λ A → nil?))) (⋯ ∷? ⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-nil , _) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon-list! nil!)) (match! N₁ ∷! match! N₂ ∷! []!)) = yes (N₂ , case-nil , det-nil case-nil)
-- 
-- pfunc-pair : PFunc CasePair
-- pfunc-pair M
--   with (case? (con? (tmCon-pair? λ A B → ⋯)) (⋯ ∷? []?)) M
-- ... | no ¬P = no λ {(_ , case-pair , _) → ¬P inhabitant}
-- ... | yes (case! (con! (tmCon-pair! (match! (x ,, y)))) (match! N ∷! []!)) =
--   yes (N · con (tmCon _ x) · con (tmCon _ y) , case-pair , det-pair case-pair)
-- 
-- ```
