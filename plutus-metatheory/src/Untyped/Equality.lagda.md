---
title: Untyped.Equality
layout: page
---
# Untyped Equality
```
module Untyped.Equality where
```

## Decidable Equality

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; isEquivalence; cong; cong₂)
open import Data.Fin using (Fin;suc;zero)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import RawU using (TmCon; tmCon; decTyTag; TyTag; ⟦_⟧tag; decTagCon; tmCon2TagCon)
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
import Data.Fin.Properties using (_≟_)
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
open import Utils as U using (Either; _×_; _,_)
import Data.List.Properties as LP using (≡-dec)
open import Builtin.Constant.AtomicType using (decAtomicTyCon)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)

```
Instances of `DecEq` will provide a Decidable Equality procedure for their type.

```
record DecEq (A : Set) : Set where
  field _≟_ : DecidableEquality A
open DecEq {{...}} public

open import Agda.Builtin.Bool using (Bool)
open import Algorithmic using (⟦_⟧)
open import Type using (Ctx⋆)
open import Type.BetaNormal using (_⊢Nf⋆_)
```

`Array` is a postulated type, so its decidable equality follows the scheme described
in "Equality of postulated types" in `Utils`: a Bool-valued primitive which is
constantly `true` in Agda and Haskell's `(==)` at runtime, turned into a decision
procedure by `U.decEqFromBool`. The only extra ingredient is `HasEq`, which carries
the `Eq` dictionary for the element type over to the Haskell side, since `(==)` on
arrays requires equality of the elements.

```
{-# FOREIGN GHC data HasEq a = Eq a => HasEq #-}
postulate
  HasEq : Set → Set
{-# COMPILE GHC HasEq = type HasEq #-}

postulate
    hasEq-TyTag : (t : TyTag) → HasEq ⟦ t ⟧tag

private
  eqArrayᵇ : {A : Set} {{HE : HasEq A}} → U.Array A → U.Array A → Bool
  eqArrayᵇ _ _ = true
  {-# COMPILE GHC eqArrayᵇ = \ _ HasEq -> (==) #-}

eqArray? : {A : Set} {{HE : HasEq A}} → DecidableEquality (U.Array A)
eqArray? {{HE}} = U.decEqFromBool (eqArrayᵇ {{HE}}) (λ _ _ → refl)


```
Several of the decision procedures depend on other `DecEq` instances, so it is useful
to give them types and bind them to instance declarations first and then use them in the
implementations further down.

```
decEq-TmCon : DecidableEquality TmCon

decEq-⟦_⟧tag : ( t : TyTag ) → DecidableEquality ⟦ t ⟧tag

decEq-⊢ : {n : ℕ} → DecidableEquality (n ⊢)

decEqList-⊢ : {n : ℕ} → DecidableEquality (List (n ⊢))

```
# Pointwise Decisions

We often need to show that one list of AST elements is equivalent to
another list of AST elements by showing the `n`th element of one is related to the
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
instance
  DecAtomicTyCon : DecEq AtomicTyCon
  DecAtomicTyCon ._≟_ = decAtomicTyCon

  DecEq-TmCon : DecEq TmCon
  DecEq-TmCon ._≟_ = decEq-TmCon

  DecEq-⊢ : ∀{n} → DecEq (n ⊢)
  DecEq-⊢ ._≟_ = decEq-⊢

  DecEq-List : ∀{n} {{DE : DecEq n}} → DecEq (List n)
  DecEq-List {{DE}} = record {_≟_ =  LP.≡-dec (DecEq._≟_ DE)}

  DecEq-Builtin : DecEq Builtin
  DecEq-Builtin ._≟_ = decBuiltin

  DecEq-ℕ : DecEq ℕ
  DecEq-ℕ ._≟_ = Data.Nat.Properties._≟_

  DecEq-ℤ : DecEq ℤ
  DecEq-ℤ ._≟_ = Data.Integer.Properties._≟_

  DecEq-Fin : ∀ {n} → DecEq (Fin n)
  DecEq-Fin ._≟_ = Data.Fin.Properties._≟_

  DecEq-String : DecEq String
  DecEq-String ._≟_ = Data.String.Properties._≟_

  DecEq-Unit : DecEq ⊤
  DecEq-Unit ._≟_ = Data.Unit.Properties._≟_

  DecEq-Bool : DecEq Bool
  DecEq-Bool ._≟_ = Data.Bool.Properties._≟_

  DecEq-TyTag : DecEq TyTag
  DecEq-TyTag ._≟_ = decTyTag

DecEq-⟦_⟧tag : (t : TyTag) → DecEq ⟦ t ⟧tag
DecEq-⟦ t ⟧tag = record { _≟_ = decEq-⟦ t ⟧tag }

listDec : {A : Set} → DecidableEquality A → DecidableEquality (U.List A)
listDec _ U.[] U.[] = yes refl
listDec _ U.[] (x U.∷ ls₂) = no (λ ())
listDec _ (x₁ U.∷ ls₁) U.[] = no (λ ())
listDec _≟_ (x₁ U.∷ ls₁) (x₂ U.∷ ls₂) with x₁ ≟ x₂
... | no x₁≠x₂ = no λ { refl → x₁≠x₂ refl }
... | yes p with listDec _≟_ ls₁ ls₂
...     | no ls₁≠ls₂ = no λ { refl → ls₁≠ls₂ refl }
...     | yes q = yes (cong₂ U._∷_ p q)

pairDec : {A B : Set} → DecidableEquality A → DecidableEquality B → DecidableEquality (A × B)
pairDec eqA eqB (a₁ , b₁) (a₂ , b₂) with (eqA a₁ a₂) | (eqB b₁ b₂)
... | yes p   | yes q = yes (cong₂ U._,_ p q)
... | no a₁≠a₂ | _ = no λ { refl → a₁≠a₂ refl }
... | _             | no b₁≠b₂ = no λ { refl → b₁≠b₂ refl }

decEqList-⊢ [] [] = yes refl
decEqList-⊢ [] (x ∷ ls₂) = no (λ ())
decEqList-⊢ (x₁ ∷ ls₁) [] = no (λ ())
decEqList-⊢ (x₁ ∷ ls₁) (x₂ ∷ ls₂) with decEq-⊢ x₁ x₂ | decEqList-⊢ ls₁ ls₂
... | yes p | yes q = yes (cong₂ _∷_ p q)
... | yes _ | no ¬q = no λ { refl → ¬q refl }
... | no ¬p | _     = no λ { refl → ¬p refl }

instance
  DecEq-UList : ∀{n} {{DE : DecEq n}} → DecEq (U.List n)
  DecEq-UList {{DE}} = record {_≟_ =  listDec (DecEq._≟_ DE)}

  DecEq-Pair : {A B : Set} {{DE-A : DecEq A}} {{DE-B : DecEq B}} → DecEq (A × B)
  DecEq-Pair {{DE-A}} {{DE-B}} = record { _≟_ = pairDec (DecEq._≟_ DE-A) (DecEq._≟_ DE-B) }

```
# Decidable Equality of Builtins

We need to decide equality between our builtin types. For the types implemented in
Agda this is unproblematic. The postulated types (`ByteString`, the BLS12-381
element types, `Value`, and `Array`) are handled by the scheme described in
"Equality of postulated types" in `Utils`, which injects Haskell's `(==)` at
runtime while remaining sound at type-checking time.

Why not just implement the builtin types in Agda? The problem is that Agda's FFI
only allows non-postulated Agda types which are representationally equivalent to
the Haskell types they compile to. If we were to implement the types in Agda, they
would need to be equivalent to the highly optimized and complicated Haskell types,
and this is not feasible.

We also cannot de-couple the Agda types from the Haskell types because the Agda
specification of UPLC is also used in conformance testing.

```
decEq-Array-⟦_⟧tag
  : (t : TyTag)
  → DecidableEquality ⟦ _⊢♯.array t ⟧tag
decEq-Array-⟦ t ⟧tag = eqArray? {{hasEq-TyTag t}}
```
# Decidable Equality for TmCon

The `TmCon` type inserts constants into Terms, so it is built from the
type tag and semantics equality decision procedures.

```

decEq-⟦ _⊢♯.atomic AtomicTyCon.aInteger ⟧tag = Data.Integer.Properties._≟_
decEq-⟦ _⊢♯.atomic AtomicTyCon.aBytestring ⟧tag = U.eqByteString?
decEq-⟦ _⊢♯.atomic AtomicTyCon.aString ⟧tag = Data.String.Properties._≟_
decEq-⟦ _⊢♯.atomic AtomicTyCon.aUnit ⟧tag = Data.Unit.Properties._≟_
decEq-⟦ _⊢♯.atomic AtomicTyCon.aBool ⟧tag = Data.Bool.Properties._≟_
decEq-⟦ _⊢♯.atomic AtomicTyCon.aData ⟧tag = U.eqDATA?
decEq-⟦ _⊢♯.atomic AtomicTyCon.aValue ⟧tag = U.eqValue?
decEq-⟦ _⊢♯.atomic AtomicTyCon.aBls12-381-g1-element ⟧tag = U.eqBls12-381-G1-Element?
decEq-⟦ _⊢♯.atomic AtomicTyCon.aBls12-381-g2-element ⟧tag = U.eqBls12-381-G2-Element?
decEq-⟦ _⊢♯.atomic AtomicTyCon.aBls12-381-mlresult ⟧tag = U.eqBls12-381-MlResult?
decEq-⟦ _⊢♯.list t ⟧tag U.[] U.[] = yes refl
decEq-⟦ _⊢♯.list t ⟧tag U.[] (x U.∷ v₁) = no λ ()
decEq-⟦ _⊢♯.list t ⟧tag (x U.∷ v) U.[] = no (λ ())
decEq-⟦ _⊢♯.list t ⟧tag (x U.∷ v) (x₁ U.∷ v₁) with decEq-⟦ t ⟧tag x x₁
... | no ¬x=x₁ = no λ { refl → ¬x=x₁ refl }
... | yes p with decEq-⟦ _⊢♯.list t ⟧tag v v₁
...                  | yes q = yes (cong₂ U._∷_ p q)
...                  | no ¬v=v₁ = no λ { refl → ¬v=v₁ refl }
decEq-⟦ _⊢♯.array t ⟧tag = decEq-Array-⟦ t ⟧tag
decEq-⟦ _⊢♯.pair t₁ t₂ ⟧tag (proj₁ U., proj₂) (proj₃ U., proj₄) with (decEq-⟦ t₁ ⟧tag proj₁ proj₃) ×-dec (decEq-⟦ t₂ ⟧tag proj₂ proj₄)
... | yes ( p , q ) = yes (cong₂ U._,_ p q)
... | no ¬pq = no λ { refl → ¬pq (refl , refl) }

decEq-TmCon (tmCon t x) (tmCon t₁ x₁) with t ≟ t₁
... | no ¬t=t₁ = no λ { refl → ¬t=t₁ refl }
... | yes refl with decEq-⟦ t ⟧tag x x₁
...   | yes p = yes (cong (tmCon t) p)
...   | no ¬p = no λ { refl → ¬p refl }

```
The Decidable Equality of terms needs to use the other instances, so we can present
that now.
```
decEq-⊢ (` x) (` x₁) with Data.Fin.Properties._≟_ x x₁
... | yes p = yes (cong ` p)
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
decEq-⊢ (t · t₂) (t₁ · t₃) with t ≟ t₁ | t₂ ≟ t₃
... | yes p | yes q = yes (cong₂ _·_ p q)
... | yes _ | no ¬q = no λ { refl → ¬q refl }
... | no ¬p | _     = no λ { refl → ¬p refl }
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
... | yes p = yes (cong force p)
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
... | yes p = yes (cong delay p)
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
... | yes p = yes (cong con p)
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
decEq-⊢ (constr i xs) (constr i₁ xs₁) with i ≟ i₁ | decEqList-⊢ xs xs₁
... | yes p | yes q = yes (cong₂ constr p q)
... | yes _ | no ¬q = no λ { refl → ¬q refl }
... | no ¬p | _     = no λ { refl → ¬p refl }
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
decEq-⊢ (case t ts) (case t₁ ts₁) with decEq-⊢ t t₁ | decEqList-⊢ ts ts₁
... | yes p | yes q = yes (cong₂ case p q)
... | yes _ | no ¬q = no λ { refl → ¬q refl }
... | no ¬p | _     = no λ { refl → ¬p refl }
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
... | yes p = yes (cong builtin p)
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
