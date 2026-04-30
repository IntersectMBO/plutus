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
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; _∷_; []; map; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Product using (_×_; proj₁; proj₂; _,_; ∃)

open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_; _⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Untyped
open import Builtin using (Builtin; ifThenElse)
open import Untyped.Equality
open import Untyped.Relation.Binary
open import Untyped.Relation.Binary.Modular hiding (_<|>_)
open import VerifiedCompilation.UntypedViews
import VerifiedCompilation.UCaseReduce as CR
```

## Generalized variables

Note: for inductives, these variables become an _index_, not a parameter! This influences the
position where this variable occurs.

```
variable
  X : ℕ
  i j : ℕ  -- indices of constr
  i' j' : ℕ  -- indices of constr

-- variable
--   M N L T : X ⊢
--   Ms Ns Ts : List (X ⊢)
--   M' N' L' T' : X ⊢
--   Ms' Ns' Ts' Ts'' : List (X ⊢)
--   K : TmCon
```


## Translation Relation

There are two transformation rules that this pass does:

### Rule: Case-Of-Case

This rule of the relation considers an expression of the form `case (case M Ms)
Ns` where all alternatives Ms are constants or SOP constructors. We call those
terms scrutinizable.

```
data Scrutinizable : X ⊢ → Set where
  scrut-constr :
    ∀ {Ms : List (X ⊢)}
    -----------------------------
    → Scrutinizable (constr i Ms)

  scrut-con :
    ∀ {K}
    ---------------------------
    → Scrutinizable (con {X} K)
```

Each branch `N` in the inner `case` must be scrutinizable, so that they can be
used as scrutinee in the cases in each resulting branch. Each `N` must be
transformed to a case that scrutinizes `N` and then uses the original branches
`outers`.

The `CaseCase` rule captures these two conditions:

```
data CaseCase (@++ R : Relation) : Relation where
  caseCase :
    ∀ {X} {M : X ⊢} {inners outers : List (X ⊢)}
    -- → All Scrutinizable inners
    ----------------------------------------------------
    → CaseCase R 
        (case (case M inners) outers)
        (case M (map (λ N → case N outers) inners))

-- If this use of `map` turns out to be hard to decide by a decision procedure,
-- use a Pointwise condition instead
```


```
scrutinizable? : (M : X ⊢) → Dec (Scrutinizable M)
scrutinizable? M
  with constr? ⋯ ⋯ M ⊎-dec con? ⋯ M
... | no ¬p = no λ {scrut-constr → ¬p (inj₁ inhabitant) ; scrut-con → ¬p (inj₂ inhabitant)}
... | yes (inj₁ (constr! (match! i) (match! args))) = yes scrut-constr
... | yes (inj₂ (con! K)) = yes scrut-con

```

Run the rule:


### Rule: Case-Of-If

The other rule matches a `case` where the scrutinee is an `ifThenElse` with SOP
constructors in the branches. Similarly to the case-of-case it is turned
inside-out. However, since `ifThenElse` is strict in its branches, they have to
be delayed, requiring also an additional force outside the overall expression.

```
data CaseIf (@++ R : Relation) : Relation where
  caseIf :
    ∀ {X} {i j} {M : X ⊢} {Ms Ns Ts}
    ----------------------------------------
    → CaseIf R
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
             · M
             · delay (case (constr i Ms) Ts)
             · delay (case (constr j Ns) Ts)
          )
        )
```

Computing the rule:

```

-- step-CaseIf : ∀ {R : Relation} → (M : X ⊢) → Maybe (∃ λ M' → CaseIf R M M')
-- step-CaseIf M
--   with
--    (case?
--      (
--        (force? (builtin? (_≟_ ifThenElse)))
--        ·? ⋯
--        ·? (constr? ⋯ ⋯)
--        ·? (constr? ⋯ ⋯)
--      )
--      ⋯) M
-- ... | no ¬PM = nothing
-- ... | yes (case!
--             (force! (builtin! refl)
--               ·! match! M
--               ·! constr! (match! i) (match! Ms)
--               ·! constr! (match! j) (match! Ns)
--             )
--             (match! Ts)
--           )
--   = just
--       (force
--         (
--            force (builtin ifThenElse)
--            · M
--            · delay (case (constr i Ms) Ts)
--            · delay (case (constr j Ns) Ts)
--         )
--       , caseIf
--       )
```

## Relation

We reuse the rules from the case-reduce relation, since the pass tries to
case-reduce after doing the `CaseCase` transformation:

```
open import VerifiedCompilation.UCaseReduce
  using (Reduction) -- ; cr-reduction; cr-compat; cr-trans; cr-sym; cr-refl; cr-constr)
open VerifiedCompilation.UCaseReduce.Rules using (case-constr)

_~_ : Relation
_~_ = Fix (Reduction + CompatTerm + Transitivity + Symmetry + Reflexivity + CaseIf + CaseCase + Empty)

pattern cc-case-if   = fix (inr (inr (inr (inr (inr (inl caseIf))))))
pattern cc-case-case = fix (inr (inr (inr (inr (inr (inr (inl caseCase)))))))
```

## Examples

```
private module Examples where
  open import Data.Fin
```

Here is a typical case-case term:
```
  M : 0 ⊢
  M = case
        (case
          (ƛ (` zero))
          ( constr 0 []
          ∷ constr 1 []
          ∷ []
          )
        )
        ( constr 42 []
        ∷ constr 43 []
        ∷ []
        )
```

It can be transformed (without also reducing the resulting branches):

```
  N : 0 ⊢
  N =
    case
      (ƛ (` zero))
      ( case
          (constr 0 [])
          ( constr 42 []
          ∷ constr 43 []
          ∷ []
          )
      ∷ case
          (constr 1 [])
          ( constr 42 []
          ∷ constr 43 []
          ∷ []
          )
      ∷ []
      )

  M~N : M ~ N
  M~N = cc-case-case
```

Reducing the resulting branches:

```
--  N' : 0 ⊢
--  N' =
--    case
--      (ƛ (` zero))
--      ( constr 42 []
--      ∷ constr 43 []
--      ∷ []
--      )
--
--  N~N' : N ~ N'
--  N~N' = cr-compat (compat-caseF cr-refl (cr-reduction (cr-constr (case-constr refl)) ∷ cr-reduction (inl (case-constr refl)) ∷ []))
--
--  M~N' : M ~ N'
--  M~N' = cr-trans M~N N~N'
```


Computing a step


```
step-CaseCase : (M : X ⊢) → Maybe (∃ λ M' → M ~ M')
step-CaseCase (case (case M inners) outers)
  = just
      ( case M (map (λ N → case N outers) inners)
      , cc-case-case
      )
step-CaseCase _ = nothing

step-CaseIf : (M : X ⊢) → Maybe (∃ λ M' → M ~ M')
step-CaseIf
  (case
     (
       force (builtin ifThenElse)
       · M
       · constr i Ms
       · constr j Ns
     )
     Ts
  )
  = just
      (force
        (
           force (builtin ifThenElse)
           · M
           · delay (case (constr i Ms) Ts)
           · delay (case (constr j Ns) Ts)
        )
      , cc-case-if
      )
step-CaseIf _ = nothing
```

```
open import Utils using (_<|>_)

-- reduce-step : (M : X ⊢) → Maybe (∃ λ M' → M ~ M')
-- reduce-step = ?

-- _>>=_ :
--   ∀ {M : X ⊢}
--   → Maybe (∃ λ N → M ~ N)
--   → ((L : X ⊢) → Maybe (∃ λ K → L ~ K))
--   → Maybe (∃ λ L → M ~ L)
-- nothing >>= _ = nothing
-- just (M' , P) >>= f
--   with f M'
-- ... | nothing = nothing
-- ... | just (M'' , P') = just (M'' , cr-trans P P')
-- 
-- step : (M : X ⊢) → Maybe (∃ λ M' → M ~ M')
-- step M
--   =   (step-CaseCase M >>= reduce-step)
--   <|> step-CaseIf M
```


Deciding the rule:

```
caseIf? : DecidableT CaseIf
caseIf? R? M N
  with
   (case?
     (
       (force? (builtin? (_≟_ ifThenElse)))
       ·? ⋯
       ·? (constr? ⋯ ⋯)
       ·? (constr? ⋯ ⋯)
     )
     ⋯) M
... | no ¬PM = no λ {caseIf → ¬PM inhabitant}
... | yes (case!
            (force! (builtin! refl)
              ·! match! M
              ·! constr! (match! i) (match! Ms)
              ·! constr! (match! j) (match! Ns)
            )
            (match! Ts)
          )
  with
    (force?
      (
        force? (builtin? (_≟_ ifThenElse))
        ·? (_≟_ M)
        ·? delay? (case? (constr? (_≟_ i) (_≟_ Ms)) (_≟_ Ts))
        ·? delay? (case? (constr? (_≟_ j) (_≟_ Ns)) ⋯)
      )
    ) N
... | no ¬pre = no λ {caseIf → ¬pre inhabitant}
... | yes (force!
            (force! (builtin! refl)
            ·! refl
            ·! delay! (case! (constr! refl refl) refl)
            ·! delay! (case! (constr! refl refl) (match! Ts'))
            )
          )
  with
    Ts ≟ Ts'
... | no ¬post = no λ {caseIf → ¬post inhabitant}
... | yes refl = yes caseIf

-- open CR-Dec
-- 
-- caseIf? : ∀ {R : ∀ {X} → X ⊢ → X ⊢ → Set} → (∀ {X} (N N' : X ⊢) → Dec (R N N')) → (M M' : X ⊢) → Dec (CaseIf R M M')
-- caseIf? R? M M' with
--   (case?
--     (
--       (force? (builtin? (_≟_ ifThenElse)))
--       ·? ⋯
--       ·? (constr? ⋯ ⋯)
--       ·? (constr? ⋯ ⋯)
--     )
--     ⋯) M
-- ... | no ¬PM = no λ {(caseIf _ _ _) → ¬PM inhabitant}
-- ... | yes (case! (force! (builtin! refl) ·! match! M ·! constr! (match! i) (match! Ms) ·! constr! (match! j) (match! Ns)) (match! Ts)) with
--   (force?
--     (
--       force? (builtin? (_≟_ ifThenElse))
--       ·? ⋯
--       ·? delay? ⋯
--       ·? delay? ⋯
--     )
--   ) M'
-- ... | no ¬pre = no λ {(caseIf _ _ _) → ¬pre inhabitant}
-- ... | yes (force!
--             (force! (builtin! refl)
--             ·! match! M'
--             ·! delay! (match! Ti)
--             ·! delay! (match! Tj)
--             )
--           )
--    with
--     R? M M'
--       <×> (R? (case (constr i Ms) Ts) Ti
--           ⊎-dec caseReduce? R? (case (constr i Ms) Ts) Ti)
--       <×> (R? (case (constr j Ns) Ts) Tj
--           ⊎-dec caseReduce? R? (case (constr j Ns) Ts) Tj)
-- ... | no ¬×  = no λ {(caseIf MM' MsMs' NsNs') → ¬× (MM' , MsMs' , NsNs')}
-- ... | yes (MM' , MsMs' , NsNs') = yes (caseIf MM' MsMs' NsNs')
```

## Overall decision procedure

```
-- DecidableT : ∀ {A : Set} → (A → A → Set) → (A → A → Set) → Set
-- DecidableT R S = Decidable R → Decidable S

--data CaseOfCase {X} : Rel X where
--  CC :
--      CaseIf CaseOfCase M M'
--    + CaseCase CaseOfCase M M'
--    + CompatTerm CaseOfCase M M'
--    → -------------------
--    CaseOfCase M M'

-- {-# TERMINATING #-}
-- caseOfCase? : ∀ {X} → (M M' : X ⊢) → Dec (CaseOfCase M M')
-- caseOfCase? M M'
--   with (   caseIf? caseOfCase? M M'
--        ⊎-dec caseCase? caseOfCase? M M'
--        ⊎-dec compatTerm? caseOfCase? M M'
--        )
-- ... | yes P = yes (CC P)
-- ... | no ¬P = no λ {(CC P) → ¬P P}

-- open import Data.Fin using (zero; suc)
-- 
-- test : Bool
-- test = Dec.does (caseOfCase? {1} (ƛ (` zero)) (ƛ (` (zero))))
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

-- data CoC : Relation where
--   isCoC : {X : ℕ} (b : X ⊢) (tn fn : ℕ)  (tt tt' ft ft' alts alts' : List (X ⊢)) →
--              Pointwise (Translation CoC) alts alts' →
--              Pointwise (Translation CoC) tt tt' →
--              Pointwise (Translation CoC) ft ft' →
--              CoC
--                (case
--                   (
--                     force (builtin ifThenElse)
--                     · b
--                     · constr tn tt
--                     · constr fn ft
--                   )
--                   alts
--                )
--                (force
--                  (
--                     force (builtin ifThenElse)
--                     · b
--                     · delay (case (constr tn tt') alts')
--                     · delay (case (constr fn ft') alts')
--                  )
--                )
-- 
-- CaseOfCase' : {X : ℕ} (ast : X ⊢) → (ast' : X ⊢) → Set
-- CaseOfCase' = Translation CoC

```
## Decision Procedure

Since this compiler phase is just a syntax re-arrangement in a very particular situation, we can
match on that situation in the before and after ASTs and apply the translation rule for this, or
expect anything else to be unaltered.

This translation matches on exactly one, very specific pattern. Using parameterised Views we can
detect that case. We create two "views" for the two patterns - we will tie together the variables in the
later function `isCoC?`.

```
--isCaseIfPre? : {X : ℕ} → Unary.Decidable (CaseIfPre {X})
--isCaseIfPre? t with
--  (case?
--    (
--      (force? (builtin? (_≟_ ifThenElse)))
--      ·? ⋯
--      ·? (constr? ⋯ ⋯)
--      ·? (constr? ⋯ ⋯)
--    )
--    ⋯)
--    t
--... | yes
--  ((case!
--    (force! (builtin! refl)
--     ·! (match! _)
--     ·! (constr! _ (match! _))
--     ·! (constr! _ (match! _))
--     ))
--     (match! _))
--    = yes isCaseIfPre
--... | no ¬CaseIfPre
--    = no λ { isCaseIfPre → ¬CaseIfPre inhabitant }
--
--
--
--isCaseIfPost? : {X : ℕ} → Unary.Decidable (CaseIfPost {X})
--isCaseIfPost? t with
--  (force?
--    (
--      force? (builtin? (_≟_ ifThenElse))
--      ·? ⋯
--      ·? delay? (case? (constr? ⋯ ⋯) ⋯)
--      ·? delay? (case? (constr? ⋯ ⋯) ⋯)
--    )
--  )
--  t
--... | no ¬CaseIfPost = no λ { (isCaseIfPost _ _ _ _ _ _) → ¬CaseIfPost inhabitant}
--... | yes (force! (_·!_ (_·!_ (_·!_ (force! (builtin! refl)) (match! b)) (delay! (case! (constr! (match! tn) (match! tt')) (match! alts'))) ) (delay! (case! (constr! (match! fn) (match! ft')) (match! alts''))))) with alts' ≟ alts''
--... | yes refl = yes (isCaseIfPost b tn fn tt' ft' alts')
--... | no ¬p = no λ { (isCaseIfPost .b .tn .fn .tt' .ft' .alts') → ¬p refl }
--
```
We can now create the final decision procedure. Because the translation can be applied recursively we need
the individual pattern decision `isCoC?` and the overall translation decision `isUntypedCaseOfCase?` to be mutually
recursive, so the `isUntypedCaseOfCase?` type declaration comes first, with the implementation later.

```

-- isCaseOfCase? : {X : ℕ} (ast ast' : X ⊢) → ProofOrCE (Translation CoC {X} ast ast')

-- {-# TERMINATING #-}
-- isCoC? : {X : ℕ}  (ast ast' : X ⊢) → ProofOrCE (CoC {X} ast ast')
-- isCoC? ast ast' with (isCaseIfPre? ast) ×-dec (isCaseIfPost? ast')
-- ... | no ¬cf = ce (λ { (isCoC b tn fn tt tt' ft ft' alts alts' x x₁ x₂) → ¬cf
--                                                                            (isCaseIfPre , isCaseIfPost b tn fn tt' ft' alts') } ) caseOfCaseT ast ast'
-- ... | yes (isCaseIfPre {b} {tn} {fn} {tt} {ft} {alts} , isCaseIfPost b₁ tn₁ fn₁ tt' ft' alts') with (b ≟ b₁) ×-dec (tn ≟ tn₁) ×-dec (fn ≟ fn₁)
-- ... | no ¬p = ce (λ { (isCoC .b .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬p (refl , refl , refl)}) caseOfCaseT ast ast'
-- ... | yes (refl , refl , refl) with pcePointwise caseOfCaseT isCaseOfCase? tt tt'
-- ...   | ce ¬p t b a = ce (λ { (isCoC _ .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬p x₁}) t b a
-- ...   | proof tt=tt' with pcePointwise caseOfCaseT isCaseOfCase? ft ft'
-- ...      | ce ¬p t b a = ce (λ { (isCoC _ .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬p x₂}) t b a
-- ...      | proof ft=ft' with pcePointwise caseOfCaseT isCaseOfCase? alts alts'
-- ...        | ce ¬pp t b a = ce (λ { (isCoC _ .tn .fn .tt .tt' .ft .ft' .alts .alts' x x₁ x₂) → ¬pp x}) t b a
-- ...        | proof alts=alts' = proof (isCoC b tn fn tt tt' ft ft' alts alts' alts=alts' tt=tt' ft=ft')
-- 
-- isCaseOfCase? {X} = translation? {X} caseOfCaseT isCoC?
```

Reduction step:

```
-- import VerifiedCompilation.UCaseReduce as UCR
-- 
-- mapM : ∀ {A B : Set} → (A → Maybe B) → List A → Maybe (List B)
-- mapM f [] = just []
-- mapM f (x ∷ xs) with f x
-- ... | nothing = nothing
-- ... | just x' with mapM f xs
-- ... | nothing = nothing
-- ... | just xs' = just (x' ∷ xs')
-- 
-- reduce : ∀ {X} → X ⊢ → Maybe (X ⊢)
-- reduce (case (case M Ms) Ns)
--   with all? scrutinizable? Ms
-- ... | false because _ = nothing
-- ... | true because _
--   with mapM (λ M → UCR.reduceM (case M Ns)) Ms
-- ... | nothing = nothing
-- ... | just Ms' = just (case M Ms')
-- reduce
--   (case
--     (
--       force (builtin ifThenElse)
--       · M
--       · constr i Ms
--       · constr j Ns
--     )
--     Ts
--   )
--   with UCR.reduceM (case (constr i Ms) Ts)
-- ... | nothing = nothing
-- ... | just Tsᵢ
--   with UCR.reduceM (case (constr j Ns) Ts)
-- ... | nothing = nothing
-- ... | just Tsⱼ =
--   just $
--     force
--       (force (builtin ifThenElse)
--        · M
--        · delay Tsᵢ
--        · delay Tsⱼ
--       )
-- {-# CATCHALL #-}
-- reduce M = nothing
-- 
-- norm = _↑?_ reduce
-- 
-- _≡-cc_ : Relation
-- M ≡-cc M' = norm M ≡ M'
-- 
-- decide : ∀ {X} (M M' : X ⊢) → ProofOrCE (M ≡-cc M')
-- decide M M' with norm M ≟ M'
-- ... | yes P = proof P
-- ... | no ¬P = ce ¬P CaseOfCaseT M M'

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
