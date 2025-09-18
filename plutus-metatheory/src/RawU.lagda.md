---
title: Raw - Interface to Haskell
layout: page
---

This module provides the interface between the Haskell code and the Agda code.
It replicates the Haskell representation of Raw. In particular, for term constants,
we need the following extension to be able to replicate the Haskell representation
of Universes.

```
{-# OPTIONS --type-in-type #-}

module RawU where
```

## TODO: add the rest of the builtins

After the metatheory is synced with the rest of the codebase, remove the following pragma:

```
{-# FOREIGN GHC {-# OPTIONS_GHC -Wno-incomplete-patterns #-} #-}
```

## Imports

```
open import Function using (_∘_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool;_∧_;true;false)
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;cong;cong₂)
open import Relation.Nullary using (does;yes;no;¬_)
open import Data.Unit using (⊤;tt)
open import Data.Product using (Σ;proj₁;proj₂) renaming (_,_ to _,,_)

open import Utils using (♯;ByteString;DATA;Value;List;Array;[];_∷_;_×_;_,_;eqDATA;Bls12-381-G1-Element;Bls12-381-G2-Element;Bls12-381-MlResult)
open import Utils.Decidable using (dcong;dcong₂)
import Builtin as B
open import Builtin using (Builtin;equals)
open Builtin.Builtin


open import Builtin.Signature as B using (Sig;sig;_⊢♯)
open _⊢♯
import Builtin.Constant.Type as T
open import Builtin.Constant.AtomicType using (AtomicTyCon;decAtomicTyCon)
open AtomicTyCon

open import Type using (Ctx⋆;∅)
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_)
open _⊢Nf⋆_
open _⊢Ne⋆_
open B.FromSig _⊢Nf⋆_ _⊢Ne⋆_ ne ` _·_ ^ con _⇒_   Π
     using (⊢♯2TyNe♯;sig2type;SigTy;sigTy2type;convSigTy) public
open import Algorithmic using (⟦_⟧)

{-# FOREIGN GHC {-# LANGUAGE GADTs #-} #-}
{-# FOREIGN GHC import PlutusCore #-}
{-# FOREIGN GHC import Raw #-}
```

## A (Haskell) Universe for types

The following tags use type-in-type, and map more directly to the Haskell representation
of the default universe.

Tags are indexed by the real type they represent.
The `Esc` datatype is used in the Haskell implementation to "escape" any kind into Type.
For constants, we only care about kind `*`, but we need it to match the Haskell implementation.
```
data Esc (a : Set) : Set where
{-# INJECTIVE Esc #-}
{-# COMPILE GHC Esc = data Esc () #-}

data Tag : Set → Set where
  integer              : Tag (Esc ℤ)
  bytestring           : Tag (Esc ByteString)
  string               : Tag (Esc String)
  bool                 : Tag (Esc Bool)
  unit                 : Tag (Esc ⊤)
  value                : Tag (Esc Value)
  pdata                : Tag (Esc DATA)
  pair                 : ∀{A B} → Tag (Esc A) → Tag (Esc B) → Tag (Esc (A × B))
  list                 : ∀{A} → Tag (Esc A) → Tag (Esc (List A))
  array                 : ∀{A} → Tag (Esc A) → Tag (Esc (Array A))
  bls12-381-g1-element : Tag (Esc Bls12-381-G1-Element)
  bls12-381-g2-element : Tag (Esc Bls12-381-G2-Element)
  bls12-381-mlresult   : Tag (Esc Bls12-381-MlResult)

{-# FOREIGN GHC type Tag = DefaultUni #-}
{-# FOREIGN GHC pattern TagInt                  = DefaultUniInteger  #-}
{-# FOREIGN GHC pattern TagBS                   = DefaultUniByteString #-}
{-# FOREIGN GHC pattern TagStr                  = DefaultUniString #-}
{-# FOREIGN GHC pattern TagBool                 = DefaultUniBool #-}
{-# FOREIGN GHC pattern TagUnit                 = DefaultUniUnit #-}
{-# FOREIGN GHC pattern TagData                 = DefaultUniData #-}
{-# FOREIGN GHC pattern TagValue                = DefaultUniValue #-}
{-# FOREIGN GHC pattern TagPair ta tb           = DefaultUniPair ta tb #-}
{-# FOREIGN GHC pattern TagList ta              = DefaultUniList ta #-}
{-# FOREIGN GHC pattern TagArray ta              = DefaultUniArray ta #-}
{-# FOREIGN GHC pattern TagBLS12_381_G1_Element = DefaultUniBLS12_381_G1_Element #-}
{-# FOREIGN GHC pattern TagBLS12_381_G2_Element = DefaultUniBLS12_381_G2_Element #-}
{-# FOREIGN GHC pattern TagBLS12_381_MlResult   = DefaultUniBLS12_381_MlResult #-}
{-# COMPILE GHC Tag                             = data Tag (TagInt
                                                           | TagBS
                                                           | TagStr
                                                           | TagBool
                                                           | TagUnit
                                                           | TagData
                                                           | TagValue
                                                           | TagPair
                                                           | TagList
                                                           | TagArray
                                                           | TagBLS12_381_G1_Element
                                                           | TagBLS12_381_G2_Element
                                                           | TagBLS12_381_MlResult)
#-}

```
## Raw syntax

This version is not intrinsically well-scoped. It's an easy to work
with rendering of the untyped plutus-core syntax.

##  Agda-Style universes

In the rest of the formalisation we use the following representation of type tags.

```
TyTag : Set
TyTag = 0 ⊢♯
```

TyTags can be given an interpretation as
an Agda type.

```
⟦_⟧tag : 0 ⊢♯ → Set
⟦ t ⟧tag =  ⟦ ne (⊢♯2TyNe♯ t) ⟧

```

Equality of `TyTag`s is decidable

```
decTyTag : DecidableEquality TyTag
decTyTag (atomic x) (atomic y) = dcong atomic (λ { refl  → refl }) (decAtomicTyCon x y)
decTyTag (atomic _) (list _) = no λ()
decTyTag (atomic _) (pair _ _) = no λ()
decTyTag (atomic _) (array _) = no λ()
decTyTag (list _) (atomic _) = no λ()
decTyTag (list x) (list y) = dcong list (λ { refl → refl }) (decTyTag x y)
decTyTag (list x) (array y) = no λ ()
decTyTag (list _) (pair _ _) = no λ()
decTyTag (array _) (pair _ _) = no λ()
decTyTag (array _) (atomic _) = no λ()
decTyTag (array x) (list y) = no λ ()
decTyTag (array x) (array y) = dcong array (λ { refl → refl }) (decTyTag x y)
decTyTag (pair _ _) (atomic _) = no λ()
decTyTag (pair _ _) (list _) = no λ()
decTyTag (pair _ _) (array _) = no λ()
decTyTag (pair x x') (pair y y') = dcong₂ pair (λ {refl → refl ,, refl}) (decTyTag x y) (decTyTag x' y')

```

## Term constants

Term constants are pairs of a tag and the corresponding type.

```
data TagCon : Set where
  tagCon : ∀{A} → Tag (Esc A) → A → TagCon

{-# FOREIGN GHC type TagCon = Some (ValueOf DefaultUni) #-}
{-# FOREIGN GHC pattern TagCon t x = Some (ValueOf t x) #-}
{-# COMPILE GHC TagCon = data TagCon (TagCon) #-}

decTagCon' : ∀{A B} → (t : Tag (Esc A)) → (x : A) → (t' : Tag (Esc B)) → (y : B) → Bool
decTagCon' integer i integer i'                          = does (i Data.Integer.≟ i')
decTagCon' bytestring b bytestring b'                    = equals b b'
decTagCon' string s string s'                            = does (s Data.String.≟ s')
decTagCon' bool b bool b'                                = does (b Data.Bool.≟ b')
decTagCon' unit ⊤ unit ⊤                                = true
decTagCon' pdata d pdata d'                              = eqDATA d d'
decTagCon' (pair t₁ t₂) (x₁ , x₂) (pair u₁ u₂) (y₁ , y₂) = decTagCon' t₁ x₁ u₁ y₁
                                                         ∧ decTagCon' t₂ x₂ u₂ y₂
decTagCon' (list t) [] (list t') []                      = true -- FIXME: Should compare tags
decTagCon' (list t) (x ∷ xs) (list t') (y ∷ ys)          = decTagCon' t x t' y
                                                         ∧ decTagCon' (list t) xs (list t') ys
decTagCon' (array t) x (array t') y = false -- FIXME: eqArray, but this needs reorganisation https://github.com/IntersectMBO/plutus-private/issues/1686
decTagCon' _ _ _ _                                       = false

-- Comparison of TagCon. Written with an auxiliary function to pass the termination checker.
decTagCon : (C C' : TagCon) → Bool
decTagCon (tagCon t x) (tagCon t' y) = decTagCon' t x t' y


```

Again term constants are a pair of a tag, and its meaning, except
this time the meaning is given by the semantic function ⟦_⟧tag.

```
data TmCon : Set where
  tmCon : (t : TyTag) → ⟦ t ⟧tag → TmCon

data Untyped : Set where
  UVar : ℕ → Untyped
  ULambda : Untyped → Untyped
  UApp : Untyped → Untyped → Untyped
  UCon : TagCon → Untyped
  UError : Untyped
  UBuiltin : Builtin → Untyped
  UDelay : Untyped → Untyped
  UForce : Untyped → Untyped
  UConstr : ℕ → List Untyped → Untyped
  UCase : Untyped → List Untyped → Untyped

{-# FOREIGN GHC import FFI.Untyped #-}
{-# COMPILE GHC Untyped = data UTerm (UVar | ULambda  | UApp | UCon | UError | UBuiltin | UDelay | UForce | UConstr | UCase) #-}

```

## Conversion between universe representations

We can convert between the two universe representations.
 * The universe à la Haskell, given by `Tag` and `TagCon`
 * The universe in Agda-style, given by `TyTag` and `TmCon`.

### From Haskell-style to Agda-style

```
tag2TyTag : ∀{A} → Tag A → TyTag
tag2TyTag integer = B.integer
tag2TyTag bytestring = B.bytestring
tag2TyTag string = B.string
tag2TyTag bool = B.bool
tag2TyTag unit = B.unit
tag2TyTag pdata = B.pdata
tag2TyTag value = B.value
tag2TyTag bls12-381-g1-element = B.bls12-381-g1-element
tag2TyTag bls12-381-g2-element = B.bls12-381-g2-element
tag2TyTag bls12-381-mlresult = B.bls12-381-mlresult
tag2TyTag (pair t u) = pair (tag2TyTag t) (tag2TyTag u)
tag2TyTag (list t) = list (tag2TyTag t)
tag2TyTag (array t) = array (tag2TyTag t)

tagLemma : ∀{A}(t : Tag (Esc A)) →  A ≡ ⟦ tag2TyTag t ⟧tag
tagLemma integer = refl
tagLemma bytestring = refl
tagLemma string = refl
tagLemma bool = refl
tagLemma unit = refl
tagLemma pdata = refl
tagLemma value = refl
tagLemma (pair t u) = cong₂ _×_ (tagLemma t) (tagLemma u)
tagLemma (list t) = cong List (tagLemma t)
tagLemma (array t) = cong Array (tagLemma t)
tagLemma bls12-381-g1-element = refl
tagLemma bls12-381-g2-element = refl
tagLemma bls12-381-mlresult = refl

tagCon2TmCon : TagCon → TmCon
tagCon2TmCon (tagCon integer x) = tmCon (B.integer) x
tagCon2TmCon (tagCon bytestring x) = tmCon (B.bytestring) x
tagCon2TmCon (tagCon string x) = tmCon (B.string) x
tagCon2TmCon (tagCon bool x) = tmCon (B.bool) x
tagCon2TmCon (tagCon unit x) = tmCon (B.unit) tt
tagCon2TmCon (tagCon pdata x) = tmCon (B.pdata) x
tagCon2TmCon (tagCon value x) = tmCon (B.value) x
tagCon2TmCon (tagCon bls12-381-g1-element x) = tmCon (B.bls12-381-g1-element) x
tagCon2TmCon (tagCon bls12-381-g2-element x) = tmCon (B.bls12-381-g2-element) x
tagCon2TmCon (tagCon bls12-381-mlresult x) = tmCon (B.bls12-381-mlresult) x
tagCon2TmCon (tagCon (pair x y) (a , b))
   rewrite tagLemma x | tagLemma y = tmCon (pair (tag2TyTag x) (tag2TyTag y)) (a , b)
tagCon2TmCon (tagCon (list x) xs) rewrite tagLemma x = tmCon (list (tag2TyTag x)) xs
tagCon2TmCon (tagCon (array x) xs) rewrite tagLemma x = tmCon (array (tag2TyTag x)) xs
```

### From Agda-style to Haskell-style

```
tyTag2Tag : TyTag → Σ Set (λ A → Tag (Esc A))
tyTag2Tag (atomic aInteger) = ℤ ,, integer
tyTag2Tag (atomic aBytestring) = ByteString ,, bytestring
tyTag2Tag (atomic aString) = String ,, string
tyTag2Tag (atomic aUnit) = ⊤ ,, unit
tyTag2Tag (atomic aBool) = Bool ,, bool
tyTag2Tag (atomic aData) = DATA ,, pdata
tyTag2Tag (atomic aValue) = Value ,, value
tyTag2Tag (atomic aBls12-381-g1-element) = Bls12-381-G1-Element ,, bls12-381-g1-element
tyTag2Tag (atomic aBls12-381-g2-element) = Bls12-381-G2-Element ,, bls12-381-g2-element
tyTag2Tag (atomic aBls12-381-mlresult) = Bls12-381-MlResult ,, bls12-381-mlresult
tyTag2Tag (list t)  with tyTag2Tag t
... | A ,, a = List A ,, list a
tyTag2Tag (array t)  with tyTag2Tag t
... | A ,, a = Array A ,, array a
tyTag2Tag (pair t u)  with tyTag2Tag t | tyTag2Tag u
... | A ,, a | B ,, b  = (A × B) ,, pair a b

tyTagLemma : (t : TyTag) → ⟦ t ⟧tag ≡ proj₁ (tyTag2Tag t)
tyTagLemma (atomic aInteger) = refl
tyTagLemma (atomic aBytestring) = refl
tyTagLemma (atomic aString) = refl
tyTagLemma (atomic aUnit) = refl
tyTagLemma (atomic aBool) = refl
tyTagLemma (atomic aData) = refl
tyTagLemma (atomic aValue) = refl
tyTagLemma (atomic aBls12-381-g1-element) = refl
tyTagLemma (atomic aBls12-381-g2-element) = refl
tyTagLemma (atomic aBls12-381-mlresult) = refl
tyTagLemma (list t) = cong List (tyTagLemma t)
tyTagLemma (array t) = cong Array (tyTagLemma t)
tyTagLemma (pair t u) = cong₂ _×_ (tyTagLemma t) (tyTagLemma u)

tmCon2TagCon : TmCon → TagCon
tmCon2TagCon (tmCon (atomic aInteger) x) = tagCon integer x
tmCon2TagCon (tmCon (atomic aBytestring) x) = tagCon bytestring x
tmCon2TagCon (tmCon (atomic aString) x) = tagCon string x
tmCon2TagCon (tmCon (atomic aUnit) x) = tagCon unit tt
tmCon2TagCon (tmCon (atomic aBool) x) = tagCon bool x
tmCon2TagCon (tmCon (atomic aData) x) = tagCon pdata x
tmCon2TagCon (tmCon (atomic aValue) x) = tagCon value x
tmCon2TagCon (tmCon (atomic aBls12-381-g1-element) x) = tagCon bls12-381-g1-element x
tmCon2TagCon (tmCon (atomic aBls12-381-g2-element) x) = tagCon bls12-381-g2-element x
tmCon2TagCon (tmCon (atomic aBls12-381-mlresult) x) = tagCon bls12-381-mlresult x
tmCon2TagCon (tmCon (list t) x) rewrite tyTagLemma t = tagCon (list (proj₂ (tyTag2Tag t))) x
tmCon2TagCon (tmCon (array t) x) rewrite tyTagLemma t = tagCon (array (proj₂ (tyTag2Tag t))) x
tmCon2TagCon (tmCon (pair t u) (x , y)) rewrite tyTagLemma t | tyTagLemma u =
    tagCon (pair (proj₂ (tyTag2Tag t)) (proj₂ (tyTag2Tag u))) (x , y)
```
