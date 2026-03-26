---
title: VerifiedCompilation.UCaseOfCas
layout: page
---
# Untyped Case of Case Translation Phase

```
module VerifiedCompilation.UCaseOfCase where

```
## Imports

```
open import Untyped.Equality using (DecEq; _≟_; decPointwise)
open import Builtin.Signature as B using (_⊢♯)
open _⊢♯
open import Builtin.Constant.AtomicType
open import VerifiedCompilation.UntypedViews -- using (Pred; isCase?; isApp?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; pcePointwise; caseOfCaseT)
open import VerifiedCompilation.Compatibility

open import Untyped.CEK using (lookup?)
open import Untyped.Reduction using (iterApp)
open import Utils using (just; nothing) renaming (_,_ to _,,_; _∷_ to cons; [] to nil)
open import Relation.Binary as Binary using (Decidable)
import Relation.Unary as Unary using (Decidable)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Untyped.CEK using (BApp; fullyAppliedBuiltin; BUILTIN; stepper; State; Stack)
open import Evaluator.Base using (maxsteps)
open import Builtin using (Builtin; ifThenElse)
open import Data.Product using (_×_; proj₁; proj₂; _,_; ∃)
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_; _because_)
open import Relation.Nullary using () renaming (_×-dec_ to _<×>_ ; _⊎-dec_ to _<+>_)
open import Data.Nat using (ℕ; suc)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; isEquivalence; cong; subst)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise; _∷_; [])
open import Data.Product using (_,_)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; _∷_; [])
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List.Relation.Unary.All using (All ; all?)
open import RawU
open import Data.Fin using (Fin)
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _+_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Function using (_∘_; case_of_; _$_)
open import Untyped.Transform
```

## Translation Relation

This compiler stage only applies to the very specific case where an `IfThenElse` builtin exists in a `case` expression.
It moves the `IfThenElse` outside and creates two `case` expressions with each of the possible lists of cases.



### Case-of-Case

Generalizable varibles save a lot of explicit ∀ binding sites.

Note: for inductives, these variables become an _index_, not a parameter! This influences the
position where this variable occurs.

```
variable
  X : ℕ
  i j : ℕ  -- indices of constr
  i' j' : ℕ  -- indices of constr

variable
  M N L T : X ⊢
  Ms Ns Ts : List (X ⊢)
  M' N' L' T' : X ⊢
  Ms' Ns' Ts' Ts'' : List (X ⊢)
  K : TmCon


```

### Case-Reduce

Some of the rules in the translation relation will reduce `case` of a constant:

```
data CR-constr (R : Rel X) : Rel X where
  cr-constr : ∀ {args} →
    lookup? i Ns ≡ just N →
    R (iterApp N args) T' →
    ------------------------------------
    CR-constr R (case (constr i args) Ns) T'

data CR-unit (R : Rel X) : Rel X where
  cr-unit : ∀ {v} →
    R N N' →
    -------------------------------------------------------------------
    CR-unit R (case (con (tmCon (atomic aUnit) v)) (N ∷ [])) N'

data CR-false (R : Rel X) : Rel X where
  cr-false :
    R N N' →
    -------------------------------------------------------------------
    CR-false R (case (con (tmCon (atomic aBool) false)) (N ∷ [])) N'

data CR-bool (R : Rel X) : Rel X where
  cr-bool : ∀ {b Nfalse Ntrue} →
    R (if b then Ntrue else Nfalse) N' →
    ----------------------------------------------------------
    CR-bool R (case (con (tmCon (atomic aBool) b)) (Nfalse ∷ Ntrue ∷ [])) N'

data CR-integer (R : Rel X) : Rel X where
  cr-integer :
    lookup? i Ns ≡ just N →
    R N N' →
    ---------------------------------------------------------
    CR-integer R (case (con (tmCon (atomic aInteger) (+ i))) Ns) N'

data CR-cons-1 (R : Rel X) : Rel X where
  cr-cons-1 : ∀ {A x xs} →
    R (N · con (tmCon A x) · con (tmCon (list A) xs)) N' →
    --------------------------------------------------------
    CR-cons-1 R (case (con (tmCon (list A) (cons x xs))) (N ∷ [])) N'

data CR-cons-2 (R : Rel X) : Rel X where
  cr-cons-2 : ∀ {A x xs Ncons Nnil} →
    R (Ncons · con (tmCon A x) · con (tmCon (list A) xs)) N' →
    -----------------------------------------------------------------
    CR-cons-2 R (case (con (tmCon (list A) (cons x xs))) (Ncons ∷ Nnil ∷ [])) N'

data CR-nil (R : Rel X) : Rel X where
  cr-nil : ∀ {A Ncons Nnil} →
    R Nnil N' →
    -----------------------------------------------------------------
    CR-nil R (case (con (tmCon (list A) nil)) (Ncons ∷ Nnil ∷ [])) N'


data CR-pair (R : Rel X) : Rel X where
  cr-pair : ∀ {A B x y} →
    R (N · (con (tmCon A x)) · (con (tmCon B y))) N' →
    ---------------------------------------------------------------
    CR-pair R (case (con (tmCon (pair A B) (x ,, y ))) (N ∷ [])) N'


CaseReduce = CR-constr
```

### Rule: Case-Of-Case

This rule of the relation considers an expression of the form `case (case M Ms)
Ns` where all alternatives Ms are constants or SOP constructors. We call those
terms scrutinizable.

```
data Scrutinizable : X ⊢ → Set where
  scrut-constr :
    Scrutinizable (constr i Ms)

  scrut-con :
    Scrutinizable (con {X} K)
```

Each branch `M` in the inner `case` (which must be scrutinizable) is related to
a branch `T` of the new outer `case`. Either through `CaseReduce` or directly through the relation R.

The `CaseCase` rule captures the transformation:

```
data CaseCase (R : Rel X) : Rel X where
  caseCase :
    R L L' →
    All Scrutinizable Ms →
    Pointwise (λ M T → CaseReduce R (case M Ns) T + R (case M Ns) T) Ms Ts →
    ----------------------
    CaseCase R
      (case (case L Ms) Ns)
      (case L' Ts)
```


```
scrutinizable? : (M : X ⊢) → Dec (Scrutinizable M)
scrutinizable? M
  with constr? ⋯ ⋯ M <+> con? ⋯ M
... | no ¬p = no λ {scrut-constr → ¬p (inj₁ inhabitant) ; scrut-con → ¬p (inj₂ inhabitant)}
... | yes (inj₁ (constr! (match! i) (match! args))) = yes scrut-constr
... | yes (inj₂ (con! K)) = yes scrut-con

maybe-absurd : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
maybe-absurd ()

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

module CR-Dec
  {R : ∀ {X} → X ⊢ → X ⊢ → Set}
  (R? : ∀ {X : ℕ} (N N' : X ⊢) → Dec (R N N'))
  where

  caseReduce-constr? : (M M' : X ⊢) → Dec (CR-constr R M M')
  caseReduce-constr? M M'
    with (case? (constr? ⋯ ⋯) ⋯) M
  ... | no ¬case = no λ {(cr-constr _ _) → ¬case inhabitant}
  ... | yes (case! (constr! (match! i) (match! args)) (match! Ns))
    with lookup? i Ns in eq
  ... | nothing = no λ {(cr-constr H _) → maybe-absurd (trans (sym H) eq)}
  ... | just N
    with R? (iterApp N args) M'
  ... | yes RT = yes (cr-constr eq RT)
  ... | no ¬iter = no λ { (cr-constr lookup iter) → ¬iter (subst (λ x → R (iterApp x args) M') (just-inj (trans (sym lookup) eq)) iter)}

  cr-unit? : (M M' : X ⊢) → Dec (CR-unit R M M')
  cr-unit? M M'
    with case? (con? (_≟_ (tmCon (atomic aUnit) Data.Unit.tt))) (⋯ ∷? (_≟_ [])) M
  ... | no ¬PM = no λ {(cr-unit _) → ¬PM inhabitant}
  ... | yes (case! (con! refl) (match! N ∷! refl))
    with R? N M'
  ... | no ¬NM' = no λ {(cr-unit NM') → ¬NM' NM'}
  ... | yes RMM' = yes (cr-unit RMM')

  cr-false? : (M M' : X ⊢) → Dec (CR-false R M M')
  cr-false? M M'
    with case? (con? (_≟_ (tmCon (atomic aBool) false))) (⋯ ∷? (_≟_ [])) M
  ... | no ¬PM = no λ {(cr-false _) → ¬PM inhabitant}
  ... | yes (case! (con! refl) (match! N ∷! refl))
    with R? N M'
  ... | no ¬RN = no λ {(cr-false RN) → ¬RN RN}
  ... | yes RN = yes (cr-false RN)

-- TODO: view for tmCon?

-- data CR-bool (R : Rel X) : Rel X where
--   cr-bool : ∀ {b Nfalse Ntrue} →
--     R (if b then Ntrue else Nfalse) N' →
--     ----------------------------------------------------------
--     CR-bool R (case (con (tmCon (atomic aBool) b)) (Nfalse ∷ Ntrue ∷ [])) N'
--
-- data CR-integer (R : Rel X) : Rel X where
--   cr-integer :
--     lookup? i Ns ≡ just N →
--     R N N' →
--     ---------------------------------------------------------
--     CR-integer R (case (con (tmCon (atomic aInteger) (+ i))) Ns) N'
-- 
-- data CR-cons-1 (R : Rel X) : Rel X where
--   cr-cons-1 : ∀ {A x xs} →
--     R (N · con (tmCon A x) · con (tmCon (list A) xs)) N' →
--     --------------------------------------------------------
--     CR-cons-1 R (case (con (tmCon (list A) (cons x xs))) (N ∷ [])) N'
-- 
-- data CR-cons-2 (R : Rel X) : Rel X where
--   cr-cons-2 : ∀ {A x xs Ncons Nnil} →
--     R (Ncons · con (tmCon A x) · con (tmCon (list A) xs)) N' →
--     -----------------------------------------------------------------
--     CR-cons-2 R (case (con (tmCon (list A) (cons x xs))) (Ncons ∷ Nnil ∷ [])) N'
-- 
-- data CR-nil (R : Rel X) : Rel X where
--   cr-nil : ∀ {A Ncons Nnil} →
--     R Nnil N' →
--     -----------------------------------------------------------------
--     CR-nil R (case (con (tmCon (list A) nil)) (Ncons ∷ Nnil ∷ [])) N'
-- 
-- 
-- data CR-pair (R : Rel X) : Rel X where
--   cr-pair : ∀ {A B x y} →
--     R (N · (con (tmCon A x)) · (con (tmCon B y))) N' →
--     ---------------------------------------------------------------
--     CR-pair R (case (con (tmCon (pair A B) (x ,, y ))) (N ∷ [])) N'


  caseCase? : (M M' : X ⊢) → Dec (CaseCase R M M')
  caseCase? M M'
    with (case? (case? ⋯ ⋯) ⋯) M <×> (case? ⋯ ⋯) M'
  ... | no ¬M×M' = no λ {(caseCase _ _ _) → ¬M×M' (inhabitant , inhabitant) }
  ... | yes ( case! (case! (match! M) (match! Ms)) (match! Ns)
            , case! (match! M') (match! Ts))
    with R? M M'
  ... | no ¬RMM' = no λ {(caseCase RMM' _ _) → ¬RMM' RMM'}
  ... | yes RLL'
    with all? scrutinizable? Ms
  ... | no ¬scrut = no λ {(caseCase _ scrut _) → ¬scrut scrut}
  ... | yes PMs
    with pointwise? (λ M T → caseReduce-constr? (case M Ns) T <+> R? (case M Ns) T) Ms Ts
  ... | no ¬pw = no λ {(caseCase _ _ pw) → ¬pw pw}
  ... | yes MsTs = yes (caseCase RLL' PMs MsTs)
  
  caseReduce? :
    (M M' : X ⊢) → Dec (CaseReduce R M M')
  caseReduce? = caseReduce-constr?
```

### Rule: Case-Of-If

The other rule matches a `case` where the scrutinee is an `ifThenElse` with SOP
constructors in the branches. Similarly to the case-of-case it is turned
inside-out. However, since `ifThenElse` is strict in its branches, they have to
be delayed, requiring also an additional force outside the overall expression.

```
data CaseIf (R : Rel X) : Rel X where
  caseIf : ∀ {Ti Tj} →
    R M M' →
    R (case (constr i Ms) Ts) Ti + CaseReduce R (case (constr i Ms) Ts) Ti →
    R (case (constr j Ns) Ts) Tj + CaseReduce R (case (constr j Ns) Ts) Tj →
    ------------------
    CaseIf R
      (case
         (
           force (builtin ifThenElse)
           · M
           · constr i Ms
           · constr j Ns
         )
         Ts
      )
      (force
        (
           force (builtin ifThenElse)
           · M'
           · delay Ti
           · delay Tj
        )
      )
```

For each rule, we need a decision procedure

```

open CR-Dec

caseIf? : ∀ {R : ∀ {X} → X ⊢ → X ⊢ → Set} → (∀ {X} (N N' : X ⊢) → Dec (R N N')) → (M M' : X ⊢) → Dec (CaseIf R M M')
caseIf? R? M M' with
  (case?
    (
      (force? (builtin? (_≟_ ifThenElse)))
      ·? ⋯
      ·? (constr? ⋯ ⋯)
      ·? (constr? ⋯ ⋯)
    )
    ⋯) M
... | no ¬PM = no λ {(caseIf _ _ _) → ¬PM inhabitant}
... | yes (case! (force! (builtin! refl) ·! match! M ·! constr! (match! i) (match! Ms) ·! constr! (match! j) (match! Ns)) (match! Ts)) with
  (force?
    (
      force? (builtin? (_≟_ ifThenElse))
      ·? ⋯
      ·? delay? ⋯
      ·? delay? ⋯
    )
  ) M'
... | no ¬pre = no λ {(caseIf _ _ _) → ¬pre inhabitant}
... | yes (force!
            (force! (builtin! refl)
            ·! match! M'
            ·! delay! (match! Ti)
            ·! delay! (match! Tj)
            )
          )
   with
    R? M M'
      <×> (R? (case (constr i Ms) Ts) Ti
          <+> caseReduce? R? (case (constr i Ms) Ts) Ti)
      <×> (R? (case (constr j Ns) Ts) Tj
          <+> caseReduce? R? (case (constr j Ns) Ts) Tj)
... | no ¬×  = no λ {(caseIf MM' MsMs' NsNs') → ¬× (MM' , MsMs' , NsNs')}
... | yes (MM' , MsMs' , NsNs') = yes (caseIf MM' MsMs' NsNs')
```

## Overall decision procedure

```
DecidableT : ∀ {A : Set} → (A → A → Set) → (A → A → Set) → Set
DecidableT R S = Decidable R → Decidable S

data CaseOfCase {X} : Rel X where
  CC :
      CaseIf CaseOfCase M M'
    + CaseCase CaseOfCase M M'
    + CompatTerm CaseOfCase M M'
    → -------------------
    CaseOfCase M M'

{-# TERMINATING #-}
caseOfCase? : ∀ {X} → (M M' : X ⊢) → Dec (CaseOfCase M M')
caseOfCase? M M'
  with (   caseIf? caseOfCase? M M'
       <+> caseCase? caseOfCase? M M'
       <+> compatTerm? caseOfCase? M M'
       )
... | yes P = yes (CC P)
... | no ¬P = no λ {(CC P) → ¬P P}

open import Data.Fin using (zero; suc)

test : Bool
test = Dec.does (caseOfCase? {1} (ƛ (` zero)) (ƛ (` (zero))))
```


## Old-style relation

### Case-of-If

This behaviour transforms a `case` that has a saturated `ifThenElse` as discriminee. The pattern of the pre-term:

```
data CaseIfPre {X : ℕ} : (X ⊢) → Set where
  isCaseIfPre :
    {b : X ⊢} {tn fn : ℕ}  {tt ft alts : List (X ⊢)}
    → -------------------------------
    CaseIfPre
      (
        case
          (
            force (builtin ifThenElse)
            · b
            · constr tn tt
            · constr fn ft
          )
          alts
      )
```

And the pattern we expect after:

```
data CaseIfPost {X : ℕ} : (X ⊢) → Set where
  isCaseIfPost :
    (b : (X ⊢)) (tn fn : ℕ) (tt' ft' alts' : List (X ⊢))
    → --------------------------------------------------
    CaseIfPost
      (force
        (
          force (builtin ifThenElse)
          · b
          · delay (case (constr tn tt') alts')
          · delay (case (constr fn ft') alts')
        )
      )
```

```

data CoC : Relation where
  isCoC : {X : ℕ} (b : X ⊢) (tn fn : ℕ)  (tt tt' ft ft' alts alts' : List (X ⊢)) →
             Pointwise (Translation CoC) alts alts' →
             Pointwise (Translation CoC) tt tt' →
             Pointwise (Translation CoC) ft ft' →
             CoC
               (case
                  (
                    force (builtin ifThenElse)
                    · b
                    · constr tn tt
                    · constr fn ft
                  )
                  alts
               )
               (force
                 (
                    force (builtin ifThenElse)
                    · b
                    · delay (case (constr tn tt') alts')
                    · delay (case (constr fn ft') alts')
                 )
               )

CaseOfCase' : {X : ℕ} (ast : X ⊢) → (ast' : X ⊢) → Set
CaseOfCase' = Translation CoC

```
## Decision Procedure

Since this compiler phase is just a syntax re-arrangement in a very particular situation, we can
match on that situation in the before and after ASTs and apply the translation rule for this, or
expect anything else to be unaltered.

This translation matches on exactly one, very specific pattern. Using parameterised Views we can
detect that case. We create two "views" for the two patterns - we will tie together the variables in the
later function `isCoC?`.

```
isCaseIfPre? : {X : ℕ} → Unary.Decidable (CaseIfPre {X})
isCaseIfPre? t with
  (case?
    (
      (force? (builtin? (_≟_ ifThenElse)))
      ·? ⋯
      ·? (constr? ⋯ ⋯)
      ·? (constr? ⋯ ⋯)
    )
    ⋯)
    t
... | yes
  ((case!
    (force! (builtin! refl)
     ·! (match! _)
     ·! (constr! _ (match! _))
     ·! (constr! _ (match! _))
     ))
     (match! _))
    = yes isCaseIfPre
... | no ¬CaseIfPre
    = no λ { isCaseIfPre → ¬CaseIfPre inhabitant }



isCaseIfPost? : {X : ℕ} → Unary.Decidable (CaseIfPost {X})
isCaseIfPost? t with
  (force?
    (
      force? (builtin? (_≟_ ifThenElse))
      ·? ⋯
      ·? delay? (case? (constr? ⋯ ⋯) ⋯)
      ·? delay? (case? (constr? ⋯ ⋯) ⋯)
    )
  )
  t
... | no ¬CaseIfPost = no λ { (isCaseIfPost _ _ _ _ _ _) → ¬CaseIfPost inhabitant}
... | yes (force! (_·!_ (_·!_ (_·!_ (force! (builtin! refl)) (match! b)) (delay! (case! (constr! (match! tn) (match! tt')) (match! alts'))) ) (delay! (case! (constr! (match! fn) (match! ft')) (match! alts''))))) with alts' ≟ alts''
... | yes refl = yes (isCaseIfPost b tn fn tt' ft' alts')
... | no ¬p = no λ { (isCaseIfPost .b .tn .fn .tt' .ft' .alts') → ¬p refl }

```
We can now create the final decision procedure. Because the translation can be applied recursively we need
the individual pattern decision `isCoC?` and the overall translation decision `isUntypedCaseOfCase?` to be mutually
recursive, so the `isUntypedCaseOfCase?` type declaration comes first, with the implementation later.

```

isCaseOfCase? : {X : ℕ} (ast ast' : X ⊢) → ProofOrCE (Translation CoC {X} ast ast')

{-# TERMINATING #-}
isCoC? : {X : ℕ}  (ast ast' : X ⊢) → ProofOrCE (CoC {X} ast ast')
isCoC? ast ast' with (isCaseIfPre? ast) ×-dec (isCaseIfPost? ast')
... | no ¬cf = ce (λ { (isCoC b tn fn tt tt' ft ft' alts alts' x x₁ x₂) → ¬cf
                                                                           (isCaseIfPre , isCaseIfPost b tn fn tt' ft' alts') } ) caseOfCaseT ast ast'
... | yes (isCaseIfPre {b} {tn} {fn} {tt} {ft} {alts} , isCaseIfPost b₁ tn₁ fn₁ tt' ft' alts') with (b ≟ b₁) ×-dec (tn ≟ tn₁) ×-dec (fn ≟ fn₁)
... | no ¬p = ce (λ { (isCoC .b .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬p (refl , refl , refl)}) caseOfCaseT ast ast'
... | yes (refl , refl , refl) with pcePointwise caseOfCaseT isCaseOfCase? tt tt'
...   | ce ¬p t b a = ce (λ { (isCoC _ .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬p x₁}) t b a
...   | proof tt=tt' with pcePointwise caseOfCaseT isCaseOfCase? ft ft'
...      | ce ¬p t b a = ce (λ { (isCoC _ .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬p x₂}) t b a
...      | proof ft=ft' with pcePointwise caseOfCaseT isCaseOfCase? alts alts'
...        | ce ¬pp t b a = ce (λ { (isCoC _ .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬pp x}) t b a
...        | proof alts=alts' = proof (isCoC b tn fn tt tt' ft ft' alts alts' alts=alts' tt=tt' ft=ft')

isCaseOfCase? {X} = translation? {X} caseOfCaseT isCoC?
```

Reduction step:

```
import VerifiedCompilation.UCaseReduce as UCR

mapM : ∀ {A B : Set} → (A → Maybe B) → List A → Maybe (List B)
mapM f [] = just []
mapM f (x ∷ xs) with f x
... | nothing = nothing
... | just x' with mapM f xs
... | nothing = nothing
... | just xs' = just (x' ∷ xs')

reduce : ∀ {X} → X ⊢ → Maybe (X ⊢)
reduce (case (case M Ms) Ns)
  with all? scrutinizable? Ms
... | false because _ = nothing
... | true because _
  with mapM (λ M → UCR.reduceM (case M Ns)) Ms
... | nothing = nothing
... | just Ms' = just (case M Ms')
reduce
  (case
    (
      force (builtin ifThenElse)
      · M
      · constr i Ms
      · constr j Ns
    )
    Ts
  )
  with UCR.reduceM (case (constr i Ms) Ts)
... | nothing = nothing
... | just Tsᵢ
  with UCR.reduceM (case (constr j Ns) Ts)
... | nothing = nothing
... | just Tsⱼ =
  just $
    force
      (force (builtin ifThenElse)
       · M
       · delay Tsᵢ
       · delay Tsⱼ
      )
{-# CATCHALL #-}
reduce M = nothing

norm = _⇑_ reduce

_≡-cc_ : Relation
M ≡-cc M' = norm M ≡ M'

decide : ∀ {X} (M M' : X ⊢) → ProofOrCE (M ≡-cc M')
decide M M' with norm M ≟ M'
... | yes P = proof P
... | no ¬P = ce ¬P caseOfCaseT M M'

```

## Semantic Equivalence

We can show that this translation never alters the semantics of the statement. This is shown
in terms of the CEK machine evaluation. Since it is a simple re-arrangement of the syntax, it
isn't a refinement argument - the state before and after the operation is the same type, and is
unaltered buy the syntax re-arrangement.

This does rely on the encoding of the semantics of `IfThenElse` in the CEK module, since we
need to show that the effective list of cases is the same as it would have been without the re-arrangement.

The `stepper` function uses the CEK machine to evaluate a term. Here we call it with a very
large gas budget and begin in an empty context (which assumes the term is closed).

```
-- TODO: Several approaches are possible.
--semantic_equivalence : ∀ {X set} {ast ast' : ⊥ ⊢}
 --                    → ⊥ ⊢̂ ast ⊳̂ ast'
 -- <Some stuff about whether one runs out of gas -- as long as neither runs out of gas, _then_ they are equivilent>
 --                    → (stepper maxsteps  (Stack.ϵ ; [] ▻ ast)) ≡ (stepper maxsteps (Stack.ε ; [] ▻ ast'))

-- ∀ {s : ℕ} → stepper s ast ≡ <valid terminate state> ⇔ ∃ { s' : ℕ } [ stepper s' ast' ≡ <same valid terminate state> ]
```
