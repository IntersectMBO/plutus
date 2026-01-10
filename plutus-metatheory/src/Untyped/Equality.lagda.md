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
open Eq using (_≡_; refl; isEquivalence; cong)
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
open import Relation.Nullary.Decidable.Core using (isYes)
open import Data.Product using (_,_)
open import Relation.Nullary using (_×-dec_)
open import Utils as U using (Either; _×_; _,_)
import Data.List.Properties as LP using (≡-dec)
open import Builtin.Constant.AtomicType using (decAtomicTyCon)
open import Agda.Builtin.TrustMe using (primTrustMe)
open import Agda.Builtin.String using (String; primStringEquality)
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

{-# FOREIGN GHC data HasEq a = Eq a => HasEq #-}
postulate
  HasEq : Set → Set
{-# COMPILE GHC HasEq = type HasEq #-}

postulate
    hasEq-TyTag : (t : TyTag) → HasEq ⟦ t ⟧tag

record HsEq (A : Set) : Set where
  field
    hsEq : A → A → Bool
open HsEq {{...}} public

-- This uses the same mechanism as eqBytestring.
-- This is only used in the decidable equality function which also
-- uses `refl` to unify the two sides and defacto confirms or refutes
-- structural equality.
eqArray : {A : Set} → {{HE : HasEq A}} → U.Array A → U.Array A → Bool
eqArray _ _ = Bool.true
{-# COMPILE GHC eqArray = \ _ HasEq -> (==) #-}

```
Several of the decision procedures depend on other `DecEq` instances, so it is useful
to give them types and bind them to instance declarations first and then use them in the
implementations further down.

```
decEq-TmCon : DecidableEquality TmCon

decEq-⟦_⟧tag : ( t : TyTag ) → DecidableEquality ⟦ t ⟧tag

decEq-⊢ : ∀{X} → DecidableEquality (X ⊢)

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

  DecEq-⊢ : ∀{X} → DecEq (X ⊢)
  DecEq-⊢ ._≟_ = decEq-⊢

  DecEq-List : ∀{X} {{DE : DecEq X}} → DecEq (List X)
  DecEq-List {{DE}} = record {_≟_ =  LP.≡-dec (DecEq._≟_ DE)}

  DecEq-Builtin : DecEq Builtin
  DecEq-Builtin ._≟_ = decBuiltin

  DecEq-ℕ : DecEq ℕ
  DecEq-ℕ ._≟_ = Data.Nat.Properties._≟_

  DecEq-ℤ : DecEq ℤ
  DecEq-ℤ ._≟_ = Data.Integer.Properties._≟_

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
... | yes refl with listDec _≟_ ls₁ ls₂
...     | no ls₁≠ls₂ = no λ { refl → ls₁≠ls₂ refl }
...     | yes refl = yes refl

pairDec : {A B : Set} → DecidableEquality A → DecidableEquality B → DecidableEquality (A × B)
pairDec eqA eqB (a₁ , b₁) (a₂ , b₂) with (eqA a₁ a₂) | (eqB b₁ b₂)
... | yes refl   | yes refl = yes refl
... | no a₁≠a₂ | _ = no λ { refl → a₁≠a₂ refl }
... | _             | no b₁≠b₂ = no λ { refl → b₁≠b₂ refl }

instance
  DecEq-UList : ∀{X} {{DE : DecEq X}} → DecEq (U.List X)
  DecEq-UList {{DE}} = record {_≟_ =  listDec (DecEq._≟_ DE)}

  DecEq-Pair : {A B : Set} {{DE-A : DecEq A}} {{DE-B : DecEq B}} → DecEq (A × B)
  DecEq-Pair {{DE-A}} {{DE-B}} = record { _≟_ = pairDec (DecEq._≟_ DE-A) (DecEq._≟_ DE-B) }

```
# Decidable Equality of Builtins

We need to decide equality between our builtin types. This is tricky because
this needs to be done at both the Agda type-checking time and at runtime, while
each stage has a completely different representation of the types.

## Type-checking time vs runtime

In Agda, the types are postulated, which means that at type-checking time we
may only rely on Agda's unification algorithm to decide equality. This can be
done by matching on `refl`, which checks whether the left hand side and the
right hand side of `≡` are definitionally equal. However, this does not translate
to the runtime stage, since at runtime the values which the `≡` type depends on
are erased. Therefore, we need to somehow "inject" a Haskell equality function which
triggers only at the runtime stage.

## Why not just implement the builtin types in Agda?

The problem is that Agda's FFI only allows non-postulated Agda types which are
representationally equivalent to the Haskell types they compile to. If we were to
implement the types in Agda, they would need to be equivalent to the highly optimized
and complicated Haskell types, and this is not feasible.

We also cannot de-couple the Agda types from the Haskell types because the Agda
specification of UPLC is also used in conformance testing.

## Using the quirks of the FFI to our advantage

Agda's FFI machinery allows us to define functions with different runtime
and type-checking definitions (see the warning at https://agda.readthedocs.io/en/v2.7.0.1/language/foreign-function-interface.html#using-haskell-functions-from-agda).
We are still constrained by the type, which needs to agree between the two
stages, so we can't just define the two implementations arbitrarily.

The simplest solution is to provide separate type-checking time and runtime definitions
for the instances of `HsEq`. During type-checking, the functions are essentially no-ops
by always returning `true`, while at runtime they defer to the Haskell implementation of
equality for each type. At type-checking time, we rely on matching on `refl` to defer to
Agda's unification algorithm, while at runtime, the matching on `refl` becomes a no-op.

```

fromDec : {A : Set} → {{DE : DecEq A}} → HsEq A
fromDec = record { hsEq = λ x₁ x₂ → isYes (x₁ ≟ x₂) }

instance
  HsEqBytestring : HsEq U.ByteString
  HsEqBytestring = record { hsEq = U.eqByteString }
  HsEqArray : {A : Set} {{HE : HasEq A}} {{HS : HsEq A}} → HsEq (U.Array A)
  HsEqArray {{HE = HE}} = record { hsEq = eqArray {{HE}}}
  HsEqList : {A : Set} {{DE : DecEq A}} → HsEq (U.List A)
  HsEqList = fromDec
  HsEqPair : {A B : Set} {{DE-A : DecEq A}} {{DE-B : DecEq B}} → HsEq (A × B)
  HsEqPair = fromDec
  HsEqBlsG1 : HsEq U.Bls12-381-G1-Element
  HsEqBlsG1 = record { hsEq = U.eqBls12-381-G1-Element }
  HsEqBlsG2 : HsEq U.Bls12-381-G2-Element
  HsEqBlsG2 = record { hsEq = U.eqBls12-381-G2-Element }
  HsEqBlsMlResult : HsEq U.Bls12-381-MlResult
  HsEqBlsMlResult = record { hsEq = U.eqBls12-381-MlResult }
  HsEqDATA : HsEq U.DATA
  HsEqDATA = record { hsEq = U.eqDATA }

HsEq-⟦_⟧tag : (t : TyTag) → HsEq ⟦ t ⟧tag
HsEq-⟦ _⊢♯.atomic AtomicTyCon.aInteger ⟧tag = fromDec
HsEq-⟦ _⊢♯.atomic AtomicTyCon.aBytestring ⟧tag = HsEqBytestring
HsEq-⟦ _⊢♯.atomic AtomicTyCon.aString ⟧tag = fromDec
HsEq-⟦ _⊢♯.atomic AtomicTyCon.aUnit ⟧tag = fromDec
HsEq-⟦ _⊢♯.atomic AtomicTyCon.aBool ⟧tag = fromDec
HsEq-⟦ _⊢♯.atomic AtomicTyCon.aData ⟧tag = HsEqDATA
HsEq-⟦ _⊢♯.atomic AtomicTyCon.aBls12-381-g1-element ⟧tag = HsEqBlsG1
HsEq-⟦ _⊢♯.atomic AtomicTyCon.aBls12-381-g2-element ⟧tag = HsEqBlsG2
HsEq-⟦ _⊢♯.atomic AtomicTyCon.aBls12-381-mlresult ⟧tag = HsEqBlsMlResult
HsEq-⟦ _⊢♯.list t ⟧tag = HsEqList {A = ⟦ t ⟧tag} {{DE = DecEq-⟦ t ⟧tag }}
HsEq-⟦ _⊢♯.array t ⟧tag = HsEqArray {A = ⟦ t ⟧tag} {{HE = hasEq-TyTag t}} {{HS = HsEq-⟦ t ⟧tag}}
HsEq-⟦ _⊢♯.pair t₁ t₂ ⟧tag = HsEqPair {A = ⟦ t₁ ⟧tag} {B = ⟦ t₂ ⟧tag} {{DE-A = DecEq-⟦ t₁ ⟧tag}} {{DE-B = DecEq-⟦ t₂ ⟧tag}}
```

## An example

Let's look at the behavior of `builtinEq (mkByteString "foo") (mkByteString "foo")` vs
`builtinEq (mkByteString "foo") (mkByteString "bar")`.

At type-checking time, if the two bytestrings are definitionally equal unification will succeed,
and the function will return `yes refl`. There is no way to return `no` because there is
no way to prove that the two terms are not equal without extra information about the
`ByteString` type. But this is enough to make Agda not succesfully type-check the program,
since it gets stuck while trying to normalize `primTrustMe`.

At runtime, `hsEq` will defer to the Haskell implementation of bytestring equality, and return
the correct result based on that. In the `yes` case, matching on `refl` will be a no-op,
while in the `no` case, we return a phony negative proof. This is safe to do because we're
at runtime and the proof gets erased anyway.

```
postulate
  magicNeg : ∀ {A : Set} {a b : A} → ¬ a ≡ b

builtinEq : {A : Set} {{HS : HsEq A}} → Binary.Decidable {A = A} _≡_
builtinEq {A} x y with hsEq x y
... | false = no magicNeg
... | true with primTrustMe {Agda.Primitive.lzero} {A} {x} {y}
...             | refl = yes refl

-- This is split out because the HTML generator can't handle double nested instance arguments!
hsEqArrayHelper : (t : TyTag) → HsEq (U.Array ⟦ t ⟧tag)
hsEqArrayHelper t = HsEqArray {A = ⟦ t ⟧tag} {{HE = hasEq-TyTag t}} {{HS = HsEq-⟦ t ⟧tag}}

decEq-Array-⟦_⟧tag :
                     (t : TyTag)
                     → DecidableEquality ⟦ _⊢♯.array t ⟧tag
decEq-Array-⟦ t ⟧tag = builtinEq {A = U.Array ⟦ t ⟧tag} {{HS = hsEqArrayHelper t}}
```
# Decidable Equality for TmCon

The `TmCon` type inserts constants into Terms, so it is built from the
type tag and semantics equality decision procedures.

```

decEq-⟦ _⊢♯.atomic AtomicTyCon.aInteger ⟧tag = Data.Integer.Properties._≟_
decEq-⟦ _⊢♯.atomic AtomicTyCon.aBytestring ⟧tag = builtinEq
decEq-⟦ _⊢♯.atomic AtomicTyCon.aString ⟧tag = Data.String.Properties._≟_
decEq-⟦ _⊢♯.atomic AtomicTyCon.aUnit ⟧tag = Data.Unit.Properties._≟_
decEq-⟦ _⊢♯.atomic AtomicTyCon.aBool ⟧tag = Data.Bool.Properties._≟_
decEq-⟦ _⊢♯.atomic AtomicTyCon.aData ⟧tag = builtinEq
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
decEq-⟦ _⊢♯.array t ⟧tag = decEq-Array-⟦ t ⟧tag
decEq-⟦ _⊢♯.pair t₁ t₂ ⟧tag (proj₁ U., proj₂) (proj₃ U., proj₄) with (decEq-⟦ t₁ ⟧tag proj₁ proj₃) ×-dec (decEq-⟦ t₂ ⟧tag proj₂ proj₄)
... | yes ( refl , refl ) = yes refl
... | no ¬pq = no λ { refl → ¬pq (refl , refl) }

decEq-TmCon (tmCon t x) (tmCon t₁ x₁) with t ≟ t₁
... | no ¬t=t₁ = no λ { refl → ¬t=t₁ refl }
... | yes refl with decEq-⟦ t ⟧tag x x₁
...   | yes refl = yes refl
...   | no ¬x=x₁ = no λ { refl → ¬x=x₁ refl }

```
The Decidable Equality of terms needs to use the other instances, so we can present
that now.
```
-- This terminating declaration shouldn't be needed?
-- It is the mutual recursion with list equality that requires it.
{-# TERMINATING #-}
decEq-⊢ (` x) (` x₁) with Data.Fin.Properties._≟_ x x₁
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
