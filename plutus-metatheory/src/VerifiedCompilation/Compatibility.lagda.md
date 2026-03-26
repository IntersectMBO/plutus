---
title: Compatibility rules for translation relations
layout: page
---
--
```
module VerifiedCompilation.Compatibility where

open import Untyped
open import VerifiedCompilation.UntypedViews
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import RawU using (TmCon)
open import Data.Nat using (ℕ ; suc)
open import Data.List using (List; [] ; _∷_)
open import Untyped.Equality using (DecEq; _≟_; decPointwise)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise; _∷_; [])
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary using () renaming (_×-dec_ to _<×>_ ; _⊎-dec_ to _<+>_)
open import Relation.Binary as Binary using (Decidable)
open import Data.Product using (_×_; _,_)
open import Data.Sum renaming (_⊎_ to _+_)

```

## Compatibility

Many translation relations have identical rules for many language constructs.
For example, in some relation `R`, we often need a rule like this for
application:

```text
R-apply :
  R M →
  R N →
  ------------
  R (M · N)
```

We call this a compatibility rule, and say `R` is compatible with `·`
constructor.

## Rules

A `Rel X` is a translation relation over terms in scope `X`.

```
Rel : ℕ → Set₁
Rel X = X ⊢ → X ⊢ → Set
```

The compatibility rules can now be given as inductives with single constructors:

```
private
  variable
    X : ℕ
    M N M' N' : X ⊢
    Ms Ns Ms' Ns' : List (X ⊢)

data CompatVar {X} : Rel X where
  `ᶜ : ∀ {x} →
    CompatVar (` x) (` x)

infixl 7 _·ᶜ_
data CompatApply {X} (R : Rel X) : Rel X where
  _·ᶜ_ :
    R M M' →
    R N N' →
    CompatApply R (M · N) (M' · N')
```

The rule for lambda is parametrized by a relation that works on any `X`, because
it will instantiate it to `X` and `suc X`

```
data CompatLam (R : ∀ {X} → Rel (suc X)) : Rel X where
  ƛᶜ : ∀ {M M' : suc X ⊢} →
    R M M' →
    CompatLam R (ƛ M) (ƛ M')

data CompatForce (R : Rel X) : Rel X where
  forceᶜ :
    R M M' →
    CompatForce R (force M) (force M')

data CompatDelay (R : Rel X) : Rel X where
  delayᶜ :
    R M M' →
    CompatDelay R (delay M) (delay M')

data CompatCase (R : Rel X) : Rel X where
  caseᶜ :
    R M M' →
    Pointwise R Ms Ms' →
    CompatCase R (case M Ms) (case M' Ms')

data CompatConstr (R : Rel X) : Rel X where
  constrᶜ : ∀ {i} →
    Pointwise R Ms Ms' →
    CompatConstr R (constr i Ms) (constr i Ms')

data CompatCon {X} : X ⊢ → X ⊢ → Set where
  conᶜ : ∀ {K} →
    CompatCon (con K) (con K)

data CompatError {X} : X ⊢ → X ⊢ → Set where
  errorᶜ :
    CompatError error error

data CompatBuiltin {X} : X ⊢ → X ⊢ → Set where
  builtinᶜ : ∀ {b} →
    CompatBuiltin (builtin b) (builtin b)
```

A relation `R` is compatible with terms when it is compatible with all constructors

```
CompatTerm : (∀ {X} → Rel X) → Rel X
CompatTerm R M M' =
      CompatApply R M M'
    + CompatVar M M'
    + CompatLam R M M'
    + CompatForce R M M'
    + CompatDelay R M M'
    + CompatConstr R M M'
    + CompatCase R M M'
    + CompatCon M M'
    + CompatBuiltin M M'
    + CompatError M M'
```

Each compatibility rule is decidable, if R is decidable:

```
compatVar? :
  Decidable (CompatVar {X})
compatVar? M M'
  with (`? ⋯) M
... | no ¬M = no λ {(`ᶜ ) → ¬M inhabitant }
... | yes (`! (match! x)) with (`? (_≟_ x) M')
...   | no ¬M' = no λ {(`ᶜ) → ¬M' inhabitant}
...   | yes (`! refl) = yes `ᶜ


compatApply? : ∀ {R : Rel X} →
  Decidable (R) →
  Decidable (CompatApply R)
compatApply? R? M M'
  with (⋯ ·? ⋯) M <×> (⋯ ·? ⋯) M'
... | no ¬MM' = no λ { (_ ·ᶜ _) → ¬MM' (inhabitant , inhabitant)}
... | yes ( match! M ·! match! N
          , match! M' ·! match! N') with R? M M' <×> R? N N'
...   | no ¬RMM'×RNN' = no λ { (RM ·ᶜ RN) → ¬RMM'×RNN' ( RM , RN )}
...   | yes (RMM' , RNN') = yes (RMM' ·ᶜ RNN')

compatLam? : ∀ {R : ∀ {X} → Rel X} →
  (∀ {X} → (M M' : X ⊢) → Dec (R M M')) →
  Decidable (CompatLam R {X})
compatLam? R? M M'
  with (ƛ? ⋯) M <×> (ƛ? ⋯) M'
... | no ¬MM' = no λ { (ƛᶜ _) → ¬MM' (inhabitant , inhabitant)}
... | yes (ƛ! (match! N) , ƛ! (match! N')) with R? N N'
...   | no ¬NN' = no λ { (ƛᶜ NN') → ¬NN' NN'}
...   | yes NN' = yes (ƛᶜ NN')

compatForce? : ∀ {R : Rel X} →
  Decidable R →
  Decidable (CompatForce R)
compatForce? R? M M'
  with force? ⋯ M <×> force? ⋯ M'
... | no ¬MM' = no λ { (forceᶜ _) → ¬MM' inhabitant}
... | yes (force! (match! N) , force! (match! N'))
  with R? N N'
...   | no ¬NN' = no λ { (forceᶜ NN) → ¬NN' NN}
...   | yes NN = yes (forceᶜ NN)

compatDelay? : ∀ {R : Rel X} →
  Decidable R →
  Decidable (CompatDelay R)
compatDelay? R? M M'
  with delay? ⋯ M <×> delay? ⋯ M'
... | no ¬MM' = no λ { (delayᶜ _) → ¬MM' inhabitant}
... | yes (delay! (match! N) , delay! (match! N'))
  with R? N N'
...   | no ¬NN' = no λ { (delayᶜ NN) → ¬NN' NN}
...   | yes NN = yes (delayᶜ NN)

pointwise? : ∀ {A B : Set} {R : A → B → Set} → (∀ x y → Dec (R x y)) → (∀ xs ys → Dec (Pointwise R xs ys))
pointwise? R? [] []         = yes []
pointwise? R? (x ∷ xs) (y ∷ ys)
  with R? x y <×> pointwise? R? xs ys
... | yes (Rxy , Rxsys) = yes (Rxy ∷ Rxsys)
... | no ¬R = no λ {(R ∷ Rs ) → ¬R (R , Rs)}
pointwise? R? (_ ∷ _) []    = no λ ()
pointwise? R? [] (_ ∷ _)    = no λ ()


compatConstr? : ∀ {R : Rel X} →
  Decidable R →
  Decidable (CompatConstr R)
compatConstr? R? M M'
  with constr? ⋯ ⋯ M
... | no ¬M = no λ { (constrᶜ _) → ¬M inhabitant}
... | yes (constr! (match! i) (match! Ms))
  with constr? (_≟_ i) ⋯ M'
... | no ¬M' = no λ { (constrᶜ _) → ¬M' inhabitant}
... | yes (constr! refl (match! Ms'))
  with pointwise? R? Ms Ms'
... | no ¬MsMs' = no λ { (constrᶜ MsMs') → ¬MsMs' MsMs'}
... | yes MsMs' = yes (constrᶜ MsMs')

compatCase? : ∀ {R : Rel X} →
  Decidable R →
  Decidable (CompatCase R)
compatCase? R? M M'
  with case? ⋯ ⋯ M <×> case? ⋯ ⋯ M'
... | no ¬MM' = no λ { (caseᶜ _ _) → ¬MM' (inhabitant , inhabitant)}
... | yes (case! (match! M) (match! Ms) , case! (match! M') (match! Ms'))
  with R? M M' <×> pointwise? R? Ms Ms'
... | no ¬MMs = no λ { (caseᶜ MM' MsMs') → ¬MMs (MM' , MsMs')}
... | yes (MM' , MsMs') = yes (caseᶜ MM' MsMs')

compatCon? : Decidable (CompatCon {X})
compatCon? M M'
  with con? ⋯ M 
... | no ¬M = no λ {conᶜ → ¬M inhabitant}
... | yes (con! (match! K))
  with con? (_≟_ K) M'
...   | no ¬M' = no λ {conᶜ → ¬M' inhabitant}
...   | yes (con! refl) = yes conᶜ


compatBuiltin? : Decidable (CompatBuiltin {X})
compatBuiltin? M M'
  with builtin? ⋯ M 
... | no ¬M = no λ {builtinᶜ → ¬M inhabitant}
... | yes (builtin! (match! K))
  with builtin? (_≟_ K) M'
...   | no ¬M' = no λ {builtinᶜ → ¬M' inhabitant}
...   | yes (builtin! refl) = yes builtinᶜ


compatError? : Decidable (CompatError {X})
compatError? M M'
  with error? M <×> error? M'
... | yes (error! , error!) = yes errorᶜ
... | no ¬MM' = no λ { errorᶜ → ¬MM' inhabitant}

```

Compatibility with terms is decidable if R is decidable

```
-- TODO: this could be faster, e.g. given an `error` term, it first has a
-- negative check in each compat check before it succeeds.
compatTerm? : ∀{X} {R : ∀ {X} → X ⊢ → X ⊢ → Set} →
  (∀ {X} → Decidable (R {X})) → Decidable (CompatTerm {X} R)
compatTerm? R? M M'
  = compatApply? R? M M'
      <+> compatVar? M M'
      <+> compatLam? R? M M'
      <+> compatForce? R? M M'
      <+> compatDelay? R? M M'
      <+> compatConstr? R? M M'
      <+> compatCase? R? M M'
      <+> compatCon? M M'
      <+> compatBuiltin? M M'
      <+> compatError? M M'




-- compatApply?' : ∀ {R : Rel X} →
--   (match ·ᵖ match) M →
--   (match ·ᵖ match) M' →
--   Decidable (R) →
--   Decidable (CompatApply R)
-- compatApply?' R? M M'
--   with (⋯ ·? ⋯) M <×> (⋯ ·? ⋯) M'
-- ... | no ¬MM' = no λ { (_ ·ᶜ _) → ¬MM' (inhabitant , inhabitant)}
-- ... | yes ( match! M ·! match! N
--           , match! M' ·! match! N') with R? M M' <×> R? N N'
-- ...   | no ¬RMM'×RNN' = no λ { (RM ·ᶜ RN) → ¬RMM'×RNN' ( RM , RN )}
-- ...   | yes (RMM' , RNN') = yes (RMM' ·ᶜ RNN')
```
