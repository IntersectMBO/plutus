---
title: VerifiedCompilation.Equality
layout: page
---
# Verified Compilation Equality
```
module VerifiedCompilation.Equality where
```

## Decidable Equivalence

There are various points in the Translation definitions where we need to compare terms
for equality. It is almost always the case that an unchanged term is a valid translation; in
many of the translations there are parts that must remain untouched. 

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; isEquivalence; cong)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import RawU using (TmCon; tmCon; decTag; TyTag; ⟦_⟧tag; decTagCon; tmCon2TagCon)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Builtin.Constant.AtomicType using (AtomicTyCon; decAtomicTyCon; ⟦_⟧at)
open import Agda.Builtin.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Data.List.Relation.Binary.Pointwise using (Pointwise-≡⇒≡; ≡⇒Pointwise-≡)
open import Data.List.Properties using (≡-dec)
open import Relation.Binary.Core using (REL)
open import Level using (Level)
open import Builtin using (Builtin; decBuiltin)
open import Builtin.Signature using (_⊢♯)
import Data.Nat.Properties using (_≟_)
open import Data.Integer using (ℤ)
import Data.Integer.Properties using (_≟_)
import Data.String.Properties using (_≟_)
import Data.Bool.Properties using (_≟_)
import Data.Unit.Properties using (_≟_)
open import Untyped using (_⊢; `; ƛ; case; constr; _·_; force; delay; con; builtin; error)
import Relation.Unary as Unary using (Decidable)
import Relation.Binary.Definitions as Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_,_)
open import Relation.Nullary using (_×-dec_)
open import Utils as U using (Maybe; nothing; just; Either)
import Data.List.Properties as LP using (≡-dec)
open import Builtin.Constant.AtomicType using (decAtomicTyCon)
open import Agda.Builtin.TrustMe using (primTrustMe)
open import Agda.Builtin.String using (String; primStringEquality)
```
Instances of `DecEq` will provide a Decidable Equality procedure for their type. 

```
record DecEq (A : Set) : Set where
  field _≟_ : DecidableEquality A
open DecEq {{...}} public
```
Several of the decision procedures depend on other `DecEq` instances, so it is useful
to give them types and bind them to instance declarations first and then use them in the
implementations further down.

```
decEq-TmCon : DecidableEquality TmCon

decEq-TyTag : DecidableEquality TyTag

decEq-⟦_⟧tag : ( t : TyTag ) → DecidableEquality ⟦ t ⟧tag
```
# Pointwise Decisions

We often need to show that one list of AST elements is a valid translation
of another list of AST elements by showing the `n`th element of one is a translation of the
`n`th element of the other, pointwise. 

```
decPointwise : {l₁ l₂ : Level} { A B : Set l₁ } { _~_ : A → B → Set l₂} → Binary.Decidable _~_ → Binary.Decidable (Pointwise _~_)
decPointwise dec [] [] = yes Pointwise.[]
decPointwise dec [] (x ∷ ys) = no (λ ())
decPointwise dec (x ∷ xs) [] = no (λ ())
decPointwise dec (x ∷ xs) (y ∷ ys) with dec x y | decPointwise dec xs ys
... | yes p | yes q = yes (p Pointwise.∷ q) 
... | yes _ | no ¬q = no λ where (_ Pointwise.∷ xs~ys) → ¬q xs~ys
... | no ¬p | _     = no λ where (x∼y Pointwise.∷ _) → ¬p x∼y
```

## Decidable Equality Instances 

Creating Instance declarations for various Decidable Equality functions to be used
when creating translation decision procedures.

```
decEq-⊢ : ∀{X} {{_ : DecEq X}} → DecidableEquality (X ⊢)

instance
  DecEq-Maybe : ∀{A} {{_ : DecEq A}} → DecEq (Maybe A)
  DecEq-Maybe ._≟_ = M.≡-dec _≟_
    where import Data.Maybe.Properties as M

  EmptyEq : DecEq ⊥
  EmptyEq = record { _≟_ = λ () }

  DecAtomicTyCon : DecEq AtomicTyCon
  DecAtomicTyCon ._≟_ = decAtomicTyCon

  DecEq-TmCon : DecEq TmCon
  DecEq-TmCon ._≟_ = decEq-TmCon

  DecEq-⊢ : ∀{X} {{_ : DecEq X}} → DecEq (X ⊢)
  DecEq-⊢ ._≟_ = decEq-⊢

  DecEq-List-⊢ : ∀{X} {{_ : DecEq X}} → DecEq (List (X ⊢))
  DecEq-List-⊢ ._≟_ = LP.≡-dec decEq-⊢

  DecEq-Builtin : DecEq Builtin
  DecEq-Builtin ._≟_ = decBuiltin

  DecEq-ℕ : DecEq ℕ
  DecEq-ℕ ._≟_ = Data.Nat.Properties._≟_

  DecEq-ℤ : DecEq ℤ
  DecEq-ℤ ._≟_ = Data.Integer.Properties._≟_

  DecEq-TyTag : DecEq TyTag
  DecEq-TyTag ._≟_ = decEq-TyTag

```
The `TmCon` type inserts constants into Terms, so it is built from the
type tag and semantics equality decision procedures. 

Type Tags (`TyTag`) are just a list of constructors to represent each
of the builtin types, or they are a structure built on top of those using
`list` or `pair`.
```
decEq-TyTag (_⊢♯.atomic x) (_⊢♯.atomic x₁) with (decAtomicTyCon x x₁)
... | yes refl = yes refl
... | no ¬x=x₁ = no λ { refl → ¬x=x₁ refl }
decEq-TyTag (_⊢♯.atomic x) (_⊢♯.list t') = no (λ ())
decEq-TyTag (_⊢♯.atomic x) (_⊢♯.pair t' t'') = no (λ ())
decEq-TyTag (_⊢♯.list t) (_⊢♯.atomic x) = no (λ ())
decEq-TyTag (_⊢♯.list t) (_⊢♯.list t') with t ≟ t'
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
decEq-TyTag (_⊢♯.list t) (_⊢♯.pair t' t'') = no (λ ())
decEq-TyTag (_⊢♯.pair t t₁) (_⊢♯.atomic x) = no (λ ())
decEq-TyTag (_⊢♯.pair t t₁) (_⊢♯.list t') = no (λ ())
decEq-TyTag (_⊢♯.pair t t₁) (_⊢♯.pair t' t'') with (t ≟ t') ×-dec (t₁ ≟ t'')
... | yes (refl , refl) = yes refl
... | no ¬pq = no λ { refl → ¬pq (refl , refl) }

```
The equality of the semantics of constants will depend on the equality of
the underlying types, so this can leverage the standard library decision
procedures. 

```
record HsEq (A : Set) : Set where
  field
    hsEq : A → A → Agda.Builtin.Bool.Bool

open HsEq {{...}} public

postulate
  magicNeg : ∀ {A : Set} {a b : A} → ¬ a ≡ b

magicBoolDec : {A : Set} → {a b : A} → Agda.Builtin.Bool.Bool → Dec (a ≡ b)
magicBoolDec true = yes primTrustMe
magicBoolDec false = no magicNeg

builtinEq : {A : Set} → Binary.Decidable {A = A} _≡_
builtinEq {A} x y with primTrustMe {Agda.Primitive.lzero} {A} {x} {y}
... | refl = yes refl

instance
  HsEqBytestring : HsEq U.ByteString
  HsEqBytestring = record { hsEq = U.eqByteString }
  HsEqBlsG1 : HsEq U.Bls12-381-G1-Element
  HsEqBlsG1 = record { hsEq = U.eqBls12-381-G1-Element }
  HsEqBlsG2 : HsEq U.Bls12-381-G2-Element
  HsEqBlsG2 = record { hsEq = U.eqBls12-381-G2-Element }
  HsEqBlsMlResult : HsEq U.Bls12-381-MlResult
  HsEqBlsMlResult = record { hsEq = U.eqBls12-381-MlResult }

decEq-⟦ _⊢♯.atomic AtomicTyCon.aInteger ⟧tag = Data.Integer.Properties._≟_
decEq-⟦ _⊢♯.atomic AtomicTyCon.aBytestring ⟧tag = builtinEq
decEq-⟦ _⊢♯.atomic AtomicTyCon.aString ⟧tag = Data.String.Properties._≟_
decEq-⟦ _⊢♯.atomic AtomicTyCon.aUnit ⟧tag = Data.Unit.Properties._≟_
decEq-⟦ _⊢♯.atomic AtomicTyCon.aBool ⟧tag = Data.Bool.Properties._≟_
-- TODO(https://github.com/IntersectMBO/plutus-private/issues/1528): why does this use magicBoolDec? surely it can be implemented correctly
decEq-⟦ _⊢♯.atomic AtomicTyCon.aData ⟧tag v v₁ = magicBoolDec (U.eqDATA v v₁)
decEq-⟦ _⊢♯.atomic AtomicTyCon.aBls12-381-g1-element ⟧tag = builtinEq
decEq-⟦ _⊢♯.atomic AtomicTyCon.aBls12-381-g2-element ⟧tag = builtinEq
decEq-⟦ _⊢♯.atomic AtomicTyCon.aBls12-381-mlresult ⟧tag = builtinEq
decEq-⟦ _⊢♯.list t ⟧tag U.[] U.[] = yes refl
decEq-⟦ _⊢♯.list t ⟧tag U.[] (x U.∷ v₁) = no λ ()
decEq-⟦ _⊢♯.list t ⟧tag (x U.∷ v) U.[] = no (λ ())
decEq-⟦ _⊢♯.list t ⟧tag (x U.∷ v) (x₁ U.∷ v₁) with decEq-⟦ t ⟧tag x x₁
... | no ¬x=x₁ = no λ { refl → ¬x=x₁ refl }
... | yes refl with decEq-⟦ _⊢♯.list t ⟧tag v v₁
...                  | yes refl = yes refl
...                  | no ¬v=v₁ = no λ { refl → ¬v=v₁ refl }
decEq-⟦ _⊢♯.pair t t₁ ⟧tag (proj₁ U., proj₂) (proj₃ U., proj₄) with (decEq-⟦ t ⟧tag proj₁ proj₃) ×-dec (decEq-⟦ t₁ ⟧tag proj₂ proj₄)
... | yes ( refl , refl ) = yes refl
... | no ¬pq = no λ { refl → ¬pq (refl , refl) } 
decEq-TmCon (tmCon t x) (tmCon t₁ x₁) with t ≟ t₁
... | no ¬t=t₁ = no λ { refl → ¬t=t₁ refl }
... | yes refl with decEq-⟦ t ⟧tag x x₁
... | yes refl = yes refl
... | no ¬x=x₁ = no λ { refl → ¬x=x₁ refl } 

```
The Decidable Equality of terms needs to use the other instances, so we can present
that now. 
```
-- This terminating declaration shouldn't be needed?
-- It is the mutual recursion with list equality that requires it. 
{-# TERMINATING #-}
decEq-⊢ (` x) (` x₁) with x ≟ x₁
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
decEq-⊢ (` x) (ƛ t₁) = no (λ ())
decEq-⊢ (` x) (t₁ · t₂) = no (λ ())
decEq-⊢ (` x) (force t₁) = no (λ ())
decEq-⊢ (` x) (delay t₁) = no (λ ())
decEq-⊢ (` x) (con x₁) = no (λ ())
decEq-⊢ (` x) (constr i xs) = no (λ ())
decEq-⊢ (` x) (case t₁ ts) = no (λ ())
decEq-⊢ (` x) (builtin b) = no (λ ())
decEq-⊢ (` x) error = no (λ ())
decEq-⊢ (ƛ t) (` x) = no (λ ())
decEq-⊢ (ƛ t) (ƛ t₁) with t ≟ t₁
... | yes p = yes (cong ƛ p)
... | no ¬p = no λ { refl → ¬p refl }
decEq-⊢ (ƛ t) (t₁ · t₂) = no (λ ())
decEq-⊢ (ƛ t) (force t₁) = no (λ ())
decEq-⊢ (ƛ t) (delay t₁) = no (λ ())
decEq-⊢ (ƛ t) (con x) = no (λ ())
decEq-⊢ (ƛ t) (constr i xs) = no (λ ())
decEq-⊢ (ƛ t) (case t₁ ts) = no (λ ())
decEq-⊢ (ƛ t) (builtin b) = no (λ ())
decEq-⊢ (ƛ t) error = no (λ ())
decEq-⊢ (t · t₂) (` x) = no (λ ())
decEq-⊢ (t · t₂) (ƛ t₁) = no (λ ())
decEq-⊢ (t · t₂) (t₁ · t₃) with (t ≟ t₁) ×-dec (t₂ ≟ t₃)
... | yes ( refl , refl )  = yes refl
... | no ¬p = no λ { refl → ¬p (refl , refl) }
decEq-⊢ (t · t₂) (force t₁) = no (λ ())
decEq-⊢ (t · t₂) (delay t₁) = no (λ ())
decEq-⊢ (t · t₂) (con x) = no (λ ())
decEq-⊢ (t · t₂) (constr i xs) = no (λ ())
decEq-⊢ (t · t₂) (case t₁ ts) = no (λ ())
decEq-⊢ (t · t₂) (builtin b) = no (λ ())
decEq-⊢ (t · t₂) error = no (λ ())
decEq-⊢ (force t) (` x) = no (λ ())
decEq-⊢ (force t) (ƛ t₁) = no (λ ())
decEq-⊢ (force t) (t₁ · t₂) = no (λ ())
decEq-⊢ (force t) (force t₁) with t ≟ t₁
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
decEq-⊢ (force t) (delay t₁) = no (λ ())
decEq-⊢ (force t) (con x) = no (λ ())
decEq-⊢ (force t) (constr i xs) = no (λ ())
decEq-⊢ (force t) (case t₁ ts) = no (λ ())
decEq-⊢ (force t) (builtin b) = no (λ ())
decEq-⊢ (force t) error = no (λ ())
decEq-⊢ (delay t) (` x) = no (λ ())
decEq-⊢ (delay t) (ƛ t₁) = no (λ ())
decEq-⊢ (delay t) (t₁ · t₂) = no (λ ())
decEq-⊢ (delay t) (force t₁) = no (λ ())
decEq-⊢ (delay t) (delay t₁) with t ≟ t₁
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
decEq-⊢ (delay t) (con x) = no (λ ())
decEq-⊢ (delay t) (constr i xs) = no (λ ())
decEq-⊢ (delay t) (case t₁ ts) = no (λ ())
decEq-⊢ (delay t) (builtin b) = no (λ ())
decEq-⊢ (delay t) error = no (λ ())
decEq-⊢ (con x) (` x₁) = no (λ ())
decEq-⊢ (con x) (ƛ t₁) = no (λ ())
decEq-⊢ (con x) (t₁ · t₂) = no (λ ())
decEq-⊢ (con x) (force t₁) = no (λ ())
decEq-⊢ (con x) (delay t₁) = no (λ ())
decEq-⊢ (con x) (con x₁) with x ≟ x₁
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
decEq-⊢ (con x) (constr i xs) = no (λ ())
decEq-⊢ (con x) (case t₁ ts) = no (λ ())
decEq-⊢ (con x) (builtin b) = no (λ ())
decEq-⊢ (con x) error = no (λ ())
decEq-⊢ (constr i xs) (` x) = no (λ ())
decEq-⊢ (constr i xs) (ƛ t₁) = no (λ ())
decEq-⊢ (constr i xs) (t₁ · t₂) = no (λ ())
decEq-⊢ (constr i xs) (force t₁) = no (λ ())
decEq-⊢ (constr i xs) (delay t₁) = no (λ ())
decEq-⊢ (constr i xs) (con x) = no (λ ())
decEq-⊢ (constr i xs) (constr i₁ xs₁) with (i ≟ i₁) ×-dec  (xs ≟ xs₁)
... | yes (refl , refl) = yes refl
... | no ¬pq = no λ { refl → ¬pq (refl , refl) } 
decEq-⊢ (constr i xs) (case t₁ ts) = no (λ ())
decEq-⊢ (constr i xs) (builtin b) = no (λ ())
decEq-⊢ (constr i xs) error = no (λ ())
decEq-⊢ (case t ts) (` x) = no (λ ())
decEq-⊢ (case t ts) (ƛ t₁) = no (λ ())
decEq-⊢ (case t ts) (t₁ · t₂) = no (λ ())
decEq-⊢ (case t ts) (force t₁) = no (λ ())
decEq-⊢ (case t ts) (delay t₁) = no (λ ())
decEq-⊢ (case t ts) (con x) = no (λ ())
decEq-⊢ (case t ts) (constr i xs) = no (λ ())
decEq-⊢ (case t ts) (case t₁ ts₁) with (decEq-⊢ t t₁) ×-dec (ts ≟ ts₁)
... | yes (refl , refl) = yes refl
... | no ¬pq = no λ { refl → ¬pq (refl , refl) } 
decEq-⊢ (case t ts) (builtin b) = no (λ ())
decEq-⊢ (case t ts) error = no (λ ())
decEq-⊢ (builtin b) (` x) = no (λ ())
decEq-⊢ (builtin b) (ƛ t₁) = no (λ ())
decEq-⊢ (builtin b) (t₁ · t₂) = no (λ ())
decEq-⊢ (builtin b) (force t₁) = no (λ ())
decEq-⊢ (builtin b) (delay t₁) = no (λ ())
decEq-⊢ (builtin b) (con x) = no (λ ())
decEq-⊢ (builtin b) (constr i xs) = no (λ ())
decEq-⊢ (builtin b) (case t₁ ts) = no (λ ())
decEq-⊢ (builtin b) (builtin b₁) with b ≟ b₁
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
decEq-⊢ (builtin b) error = no (λ ())
decEq-⊢ error (` x) = no (λ ())
decEq-⊢ error (ƛ t₁) = no (λ ())
decEq-⊢ error (t₁ · t₂) = no (λ ())
decEq-⊢ error (force t₁) = no (λ ())
decEq-⊢ error (delay t₁) = no (λ ())
decEq-⊢ error (con x) = no (λ ())
decEq-⊢ error (constr i xs) = no (λ ())
decEq-⊢ error (case t₁ ts) = no (λ ())
decEq-⊢ error (builtin b) = no (λ ())
decEq-⊢ error error = yes refl

```
