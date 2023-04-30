
This module provides the interface between the Haskell code and the Agda code.
It replicates the Haskell representation of Raw. In particular, for term constants,
we need the following extension to be able to replicate the Haskell representation
of Universes.

```
{-# OPTIONS --type-in-type #-}

module RawU where
```

## Imports

```
open import Function using (_∘_)
open import Data.Nat using (ℕ)
open import Data.Bool using (true;false)
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Bool using (Bool)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;cong;cong₂)
open import Relation.Nullary using (yes;no;¬_)
open import Data.Unit using (⊤;tt)
open import Data.Product using (Σ;proj₁;proj₂) renaming (_,_ to _,,_)

open import Utils using (ByteString;DATA;List;_×_;_,_;Bls12-381-G1-Element;Bls12-381-G2-Element;Bls12-381-MlResult)
open import Builtin using (Builtin;equals)
open Builtin.Builtin

{-# FOREIGN GHC {-# LANGUAGE GADTs #-} #-}
{-# FOREIGN GHC import PlutusCore #-}
{-# FOREIGN GHC import Raw #-}
```

## A (Haskell) Universe for types

The following tags use type-in-type, and map more directly to the Haskell representation
of the default universe.

Tags are indexed by the real type they represent.
The `Esc` datatype is used in the Haskell implementation to "escape" any kind into Type.
For constants, we only care about kind *, but we need it to match the Haskell implementation.
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
  pdata                : Tag (Esc DATA)
  pair                 : ∀{A B} → Tag (Esc A) → Tag (Esc B) → Tag (Esc (A × B))
  list                 : ∀{A} → Tag (Esc A) → Tag (Esc (List A))
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
{-# FOREIGN GHC pattern TagPair ta tb           = DefaultUniPair ta tb #-}
{-# FOREIGN GHC pattern TagList ta              = DefaultUniList ta #-}
{-# FOREIGN GHC pattern TagBLS12_381_G1_Element = DefaultUniBLS12_381_G1_Element #-}
{-# FOREIGN GHC pattern TagBLS12_381_G2_Element = DefaultUniBLS12_381_G2_Element #-}
{-# FOREIGN GHC pattern TagBLS12_381_MlResult   = DefaultUniBLS12_381_MlResult #-}
{-# COMPILE GHC Tag                             = data Tag (TagInt | TagBS | TagStr | TagBool | TagUnit | TagData | TagPair | TagList | TagBLS12_381_G1_Element | TagBLS12_381_G2_Element | TagBLS12_381_MlResult) #-}
```

## Term constants

Term constants are pairs of a tag and the corresponding type. 

```
data TagCon : Set where
  tagCon : ∀{A} → Tag (Esc A) → A → TagCon

{-# FOREIGN GHC type TagCon = Some (ValueOf DefaultUni) #-}
{-# FOREIGN GHC pattern TagCon t x = Some (ValueOf t x) #-} 
{-# COMPILE GHC TagCon = data TagCon (TagCon) #-}

decTagCon : (C C' : TagCon) → Bool
decTagCon (tagCon integer i) (tagCon integer i') with i Data.Integer.≟ i'
... | yes p = true
... | no ¬p = false
decTagCon (tagCon bytestring b) (tagCon bytestring b') with equals b b'
decTagCon (tagCon bytestring b) (tagCon bytestring b') | false = false
decTagCon (tagCon bytestring b) (tagCon bytestring b') | true = true
decTagCon (tagCon string s) (tagCon string s') with s Data.String.≟ s'
... | yes p = true
... | no ¬p = false
decTagCon (tagCon bool b) (tagCon bool b') with b Data.Bool.≟ b'
... | yes p = true
... | no ¬p = false
decTagCon (tagCon unit ⊤) (tagCon unit ⊤) = true
decTagCon _ _ = false
```
## Raw syntax

This version is not intrinsically well-scoped. It's an easy to work
with rendering of the untyped plutus-core syntax.

```
data Untyped : Set where
  UVar : ℕ → Untyped
  ULambda : Untyped → Untyped
  UApp : Untyped → Untyped → Untyped
  UCon : TagCon → Untyped
  UError : Untyped
  UBuiltin : Builtin → Untyped
  UDelay : Untyped → Untyped
  UForce : Untyped → Untyped

{-# FOREIGN GHC import Untyped #-}
{-# COMPILE GHC Untyped = data UTerm (UVar | ULambda  | UApp | UCon | UError | UBuiltin | UDelay | UForce) #-}
```

##  Agda-Style universes

In the rest of the formalisation we use the following representation of type tags.

```
data TyTag : Set where
  integer              : TyTag
  bytestring           : TyTag
  string               : TyTag
  bool                 : TyTag
  unit                 : TyTag
  pdata                : TyTag
  pair                 : TyTag → TyTag → TyTag
  list                 : TyTag → TyTag
  bls12-381-g1-element : TyTag
  bls12-381-g2-element : TyTag
  bls12-381-mlresult   : TyTag
```

The meaning of type tags is provided by the following function.

```
⟦_⟧tag : TyTag → Set
⟦ integer ⟧tag = ℤ
⟦ bytestring ⟧tag = ByteString
⟦ string ⟧tag = String
⟦ bool ⟧tag = Bool
⟦ unit ⟧tag = ⊤
⟦ pdata ⟧tag = DATA
⟦ pair p p' ⟧tag = ⟦ p ⟧tag × ⟦ p' ⟧tag
⟦ list p ⟧tag = List ⟦ p ⟧tag
⟦ bls12-381-g1-element ⟧tag = Bls12-381-G1-Element
⟦ bls12-381-g2-element ⟧tag = Bls12-381-G2-Element
⟦ bls12-381-mlresult ⟧tag = Bls12-381-MlResult
```

Equality of `TyTag`s is decidable

```
decTag : DecidableEquality TyTag
decTag integer integer = yes refl
decTag integer bytestring = no λ()
decTag integer string =  no λ()
decTag integer bool = no λ()
decTag integer unit = no λ()
decTag integer pdata = no λ()
decTag integer (pair y y₁) = no λ()
decTag integer (list y) = no λ()
decTag integer bls12-381-g1-element = no λ()
decTag integer bls12-381-g2-element = no λ()
decTag integer bls12-381-mlresult = no λ()
decTag bytestring integer = no λ()
decTag bytestring bytestring = yes refl
decTag bytestring string = no λ()
decTag bytestring bool = no λ()
decTag bytestring unit = no λ()
decTag bytestring pdata = no λ()
decTag bytestring (pair y y₁) = no λ()
decTag bytestring (list y) = no λ()
decTag bytestring bls12-381-g1-element = no λ()
decTag bytestring bls12-381-g2-element = no λ()
decTag bytestring bls12-381-mlresult = no λ()
decTag string integer = no λ()
decTag string bytestring = no λ()
decTag string string = yes refl
decTag string bool = no λ()
decTag string unit = no λ()
decTag string pdata = no λ()
decTag string (pair y y₁) = no λ()
decTag string (list y) = no λ()
decTag string bls12-381-g1-element = no λ()
decTag string bls12-381-g2-element = no λ()
decTag string bls12-381-mlresult = no λ()
decTag bool integer = no λ()
decTag bool bytestring = no λ()
decTag bool string = no λ()
decTag bool bool = yes refl
decTag bool unit = no λ()
decTag bool pdata = no λ()
decTag bool (pair y y₁) = no λ()
decTag bool (list y) = no λ()
decTag bool bls12-381-g1-element = no λ()
decTag bool bls12-381-g2-element = no λ()
decTag bool bls12-381-mlresult = no λ()
decTag unit integer = no λ()
decTag unit bytestring = no λ()
decTag unit string = no λ()
decTag unit bool = no λ()
decTag unit unit = yes refl
decTag unit pdata = no λ()
decTag unit (pair y y₁) = no λ()
decTag unit (list y) = no λ()
decTag unit bls12-381-g1-element = no λ()
decTag unit bls12-381-g2-element = no λ()
decTag unit bls12-381-mlresult = no λ()
decTag pdata integer = no λ()
decTag pdata bytestring = no λ()
decTag pdata string = no λ()
decTag pdata bool = no λ()
decTag pdata unit = no λ()
decTag pdata pdata = yes refl
decTag pdata (pair y y₁) = no λ()
decTag pdata (list y) = no λ()
decTag pdata bls12-381-g1-element = no λ()
decTag pdata bls12-381-g2-element = no λ()
decTag pdata bls12-381-mlresult = no λ()
decTag (pair x x₁) integer = no λ()
decTag (pair x x₁) bytestring = no λ()
decTag (pair x x₁) string = no λ()
decTag (pair x x₁) bool = no λ()
decTag (pair x x₁) unit = no λ()
decTag (pair x x₁) pdata = no λ()
decTag (pair x x₁) (pair y y₁) with decTag x y | decTag x₁ y₁ 
... | yes refl | yes refl = yes refl 
... | yes _    | no ¬p    = no λ {refl  → ¬p refl}
... | no ¬p    | _        = no λ {refl  → ¬p refl}
decTag (pair x x₁) (list y) = no λ()
decTag (pair x x₁) bls12-381-g1-element = no λ()
decTag (pair x x₁) bls12-381-g2-element = no λ()
decTag (pair x x₁) bls12-381-mlresult = no λ()
decTag (list x) integer =  no λ()
decTag (list x) bytestring =  no λ()
decTag (list x) string =  no λ()
decTag (list x) bool =  no λ()
decTag (list x) unit =  no λ()
decTag (list x) pdata =  no λ()
decTag (list x) (pair y y₁) =  no λ()
decTag (list x) (list y) with decTag x y 
... | yes refl = yes refl
... | no ¬p    = no λ {refl  → ¬p refl}
decTag (list x) bls12-381-g1-element =  no λ()
decTag (list x) bls12-381-g2-element =  no λ()
decTag (list x) bls12-381-mlresult =  no λ()
decTag bls12-381-g1-element integer = no λ()
decTag bls12-381-g1-element bytestring = no λ()
decTag bls12-381-g1-element string = no λ()
decTag bls12-381-g1-element bool = no λ()
decTag bls12-381-g1-element unit = no λ()
decTag bls12-381-g1-element pdata = no λ()
decTag bls12-381-g1-element (pair y y₁) = no λ()
decTag bls12-381-g1-element (list y) = no λ()
decTag bls12-381-g1-element bls12-381-g1-element = yes refl
decTag bls12-381-g1-element bls12-381-g2-element = no λ()
decTag bls12-381-g1-element bls12-381-mlresult = no λ()
decTag bls12-381-g2-element integer = no λ()
decTag bls12-381-g2-element bytestring = no λ()
decTag bls12-381-g2-element string = no λ()
decTag bls12-381-g2-element bool = no λ()
decTag bls12-381-g2-element unit = no λ()
decTag bls12-381-g2-element pdata = no λ()
decTag bls12-381-g2-element (pair y y₁) = no λ()
decTag bls12-381-g2-element (list y) = no λ()
decTag bls12-381-g2-element bls12-381-g1-element = no λ()
decTag bls12-381-g2-element bls12-381-g2-element = yes refl
decTag bls12-381-g2-element bls12-381-mlresult = no λ()
decTag bls12-381-mlresult integer = no λ()
decTag bls12-381-mlresult bytestring = no λ()
decTag bls12-381-mlresult string = no λ()
decTag bls12-381-mlresult bool = no λ()
decTag bls12-381-mlresult unit = no λ()
decTag bls12-381-mlresult pdata = no λ()
decTag bls12-381-mlresult (pair y y₁) = no λ()
decTag bls12-381-mlresult (list y) = no λ()
decTag bls12-381-mlresult bls12-381-g1-element = no λ()
decTag bls12-381-mlresult bls12-381-g2-element = no λ()
decTag bls12-381-mlresult bls12-381-mlresult = yes refl
```

Again term constants are a pair of a tag, and its meaning, except
this time the meaning is given by the semantic function ⟦_⟧tag.

```
data TmCon : Set where 
  tmCon : (t : TyTag) → ⟦ t ⟧tag → TmCon
```

## Conversion between universe representations

We can convert between the two universe representations.
 * The universe à la Haskell, given by `Tag` and `TagCon`
 * The universe in Agda-style, given by `TyTag` abd `TmCon`.

### From Haskell-style to Agda-style

```
tag2TyTag : ∀{A} → Tag A → TyTag
tag2TyTag integer = integer
tag2TyTag bytestring = bytestring
tag2TyTag string = string
tag2TyTag bool = bool
tag2TyTag unit = unit
tag2TyTag pdata = pdata
tag2TyTag (pair t u) = pair (tag2TyTag t) (tag2TyTag u)
tag2TyTag (list t) = list (tag2TyTag t)
tag2TyTag bls12-381-g1-element = bls12-381-g1-element
tag2TyTag bls12-381-g2-element = bls12-381-g2-element
tag2TyTag bls12-381-mlresult = bls12-381-mlresult


tagLemma : ∀{A}(t : Tag (Esc A)) →  A ≡ ⟦ tag2TyTag t ⟧tag
tagLemma integer = refl
tagLemma bytestring = refl
tagLemma string = refl
tagLemma bool = refl
tagLemma unit = refl
tagLemma pdata = refl
tagLemma (pair t u) = cong₂ _×_ (tagLemma t) (tagLemma u)
tagLemma (list t) = cong List (tagLemma t)
tagLemma bls12-381-g1-element = refl
tagLemma bls12-381-g2-element = refl
tagLemma bls12-381-mlresult = refl

tagCon2TmCon : TagCon → TmCon
tagCon2TmCon (tagCon integer x) = tmCon integer x
tagCon2TmCon (tagCon bytestring x) = tmCon bytestring x
tagCon2TmCon (tagCon string x) = tmCon string x
tagCon2TmCon (tagCon bool x) = tmCon bool x
tagCon2TmCon (tagCon unit x) = tmCon unit tt
tagCon2TmCon (tagCon pdata x) = tmCon pdata x
tagCon2TmCon (tagCon (pair x y) (a , b)) rewrite tagLemma x | tagLemma y = tmCon (pair (tag2TyTag x) (tag2TyTag y)) (a , b)
tagCon2TmCon (tagCon (list x) xs) rewrite tagLemma x = tmCon (list (tag2TyTag x)) xs
tagCon2TmCon (tagCon bls12-381-g1-element x) = tmCon bls12-381-g1-element x
tagCon2TmCon (tagCon bls12-381-g2-element x) = tmCon bls12-381-g2-element x
tagCon2TmCon (tagCon bls12-381-mlresult x) = tmCon bls12-381-mlresult x
```

### From Agda-style to Haskell-style

```
tyTag2Tag : TyTag → Σ Set (λ A → Tag (Esc A)) 
tyTag2Tag integer = ℤ ,, integer
tyTag2Tag bytestring = ByteString ,, bytestring
tyTag2Tag string = String ,, string
tyTag2Tag bool = Bool ,, bool
tyTag2Tag unit = ⊤ ,, unit
tyTag2Tag pdata = DATA ,, pdata
tyTag2Tag (pair t u) with tyTag2Tag t | tyTag2Tag u 
... | A ,, a | B ,, b = A × B ,, pair a b
tyTag2Tag (list t) with tyTag2Tag t 
... | A ,, a = (List A) ,, (list a)
tyTag2Tag bls12-381-g1-element = Bls12-381-G1-Element ,, bls12-381-g1-element
tyTag2Tag bls12-381-g2-element = Bls12-381-G2-Element ,, bls12-381-g2-element
tyTag2Tag bls12-381-mlresult = Bls12-381-MlResult ,, bls12-381-mlresult

tyTagLemma : (t : TyTag) → ⟦ t ⟧tag ≡ proj₁ (tyTag2Tag t)
tyTagLemma integer = refl
tyTagLemma bytestring = refl
tyTagLemma string = refl
tyTagLemma bool = refl
tyTagLemma unit = refl
tyTagLemma pdata = refl
tyTagLemma (pair t u) = cong₂ _×_ (tyTagLemma t) (tyTagLemma u)
tyTagLemma (list t) = cong List (tyTagLemma t)
tyTagLemma bls12-381-g1-element = refl
tyTagLemma bls12-381-g2-element = refl
tyTagLemma bls12-381-mlresult = refl

tmCon2TagCon : TmCon → TagCon
tmCon2TagCon (tmCon integer x) = tagCon integer x
tmCon2TagCon (tmCon bytestring x) = tagCon bytestring x
tmCon2TagCon (tmCon string x) = tagCon string x
tmCon2TagCon (tmCon bool x) = tagCon bool x
tmCon2TagCon (tmCon unit x) = tagCon unit tt
tmCon2TagCon (tmCon pdata x) = tagCon pdata x
tmCon2TagCon (tmCon (pair t u) (x , y)) rewrite tyTagLemma t | tyTagLemma u = 
    tagCon (pair (proj₂ (tyTag2Tag t)) (proj₂ (tyTag2Tag u))) (x , y)
tmCon2TagCon (tmCon (list t) x) rewrite tyTagLemma t = tagCon (list (proj₂ (tyTag2Tag t))) x
tmCon2TagCon (tmCon bls12-381-g1-element x) = tagCon bls12-381-g1-element x
tmCon2TagCon (tmCon bls12-381-g2-element x) = tagCon bls12-381-g2-element x
tmCon2TagCon (tmCon bls12-381-mlresult x) = tagCon bls12-381-mlresult x
``` 