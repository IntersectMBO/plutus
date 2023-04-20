
```
{-# OPTIONS --type-in-type #-}

module RawU where
```
## Imports



```
open import Function using (_∘_)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Bool using (Bool)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes;no;¬_)
open import Data.Unit using (⊤;tt)

open import Utils --using (ByteString;DATA;List;_×_;_,_;Maybe;just;nothing)

open import Builtin using (Builtin)
open Builtin.Builtin

```

Tags that use type in type but map more directly to the Haskell Representation

```
data Tag : Set → Set where
  integer    : Tag ℤ
  bytestring : Tag ByteString
  string     : Tag String
  bool       : Tag Bool
  unit       : Tag ⊤
  pdata      : Tag DATA
  pair       : ∀{A B} → Tag A → Tag B → Tag (A × B)
  list       : ∀{A} → Tag A → Tag (List A)

data TagTm : Set where
  tagTm : ∀{A} → Tag A → A → TagTm

{-# FOREIGN GHC type Tag a = DefaultUni a #-}
{-# FOREIGN GHC pattern TagInt        = DefaultUniInteger  #-}
{-# FOREIGN GHC pattern TagBS         = DefaultUniByteString #-}
{-# FOREIGN GHC pattern TagStr        = DefaultUniString #-}
{-# FOREIGN GHC pattern TagBool       = DefaultUniBool #-}
{-# FOREIGN GHC pattern TagUnit       = DefaultUniUnit #-}
{-# FOREIGN GHC pattern TagData       = DefaultUniData #-}
{-# FOREIGN GHC pattern TagPair ta tb = DefaultUniPair ta tb #-}
{-# FOREIGN GHC pattern TagList ta    = DefaultUniList ta #-}
{-# COMPILE GHC Tag = data Tag (TagInt | TagBS | TagStr | TagBool | TagUnit | TagData | TagPair | TagList) #-}


```
## TyTags

Type Tags could be defined as

data TyTag : Set
TyTag = 0 ⊢♯

But since we want to use them to interface with Haskell code,
we define them directly here.

```
data TyTag : Set where
  integer    : TyTag
  bytestring : TyTag
  string     : TyTag
  bool       : TyTag
  unit       : TyTag
  pdata      : TyTag
  pair       : TyTag → TyTag → TyTag
  list       : TyTag → TyTag

⟦_⟧tag : TyTag → Set
⟦ integer ⟧tag = ℤ
⟦ bytestring ⟧tag = ByteString
⟦ string ⟧tag = String
⟦ bool ⟧tag = Bool
⟦ unit ⟧tag = ⊤
⟦ pdata ⟧tag = DATA
⟦ pair p p' ⟧tag = ⟦ p ⟧tag × ⟦ p' ⟧tag
⟦ list p ⟧tag = List ⟦ p ⟧tag

decTag : DecidableEquality TyTag
decTag integer integer = yes refl
decTag integer bytestring = no λ()
decTag integer string =  no λ()
decTag integer bool = no λ()
decTag integer unit = no λ()
decTag integer pdata = no λ()
decTag integer (pair y y₁) = no λ()
decTag integer (list y) = no λ()
decTag bytestring integer = no λ()
decTag bytestring bytestring = yes refl
decTag bytestring string = no λ()
decTag bytestring bool = no λ()
decTag bytestring unit = no λ()
decTag bytestring pdata = no λ()
decTag bytestring (pair y y₁) = no λ()
decTag bytestring (list y) = no λ()
decTag string integer = no λ()
decTag string bytestring = no λ()
decTag string string = yes refl
decTag string bool = no λ()
decTag string unit = no λ()
decTag string pdata = no λ()
decTag string (pair y y₁) = no λ()
decTag string (list y) = no λ()
decTag bool integer = no λ()
decTag bool bytestring = no λ()
decTag bool string = no λ()
decTag bool bool = yes refl
decTag bool unit = no λ()
decTag bool pdata = no λ()
decTag bool (pair y y₁) = no λ()
decTag bool (list y) = no λ()
decTag unit integer = no λ()
decTag unit bytestring = no λ()
decTag unit string = no λ()
decTag unit bool = no λ()
decTag unit unit = yes refl
decTag unit pdata = no λ()
decTag unit (pair y y₁) = no λ()
decTag unit (list y) = no λ()
decTag pdata integer = no λ()
decTag pdata bytestring = no λ()
decTag pdata string = no λ()
decTag pdata bool = no λ()
decTag pdata unit = no λ()
decTag pdata pdata = yes refl
decTag pdata (pair y y₁) = no λ()
decTag pdata (list y) = no λ()
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

{-# COMPILE GHC TyTag = data TyTag (TagInt | TagBS | TagStr | TagBool | TagUnit | TagData | TagPair | TagList) #-}
```
## Raw syntax

This version is not intrinsically well-scoped. It's an easy to work
with rendering of the untyped plutus-core syntax.

The term constants `TermCon` are easy to interface with Haskell, but the list 
representation is not very good as it allows heterogenous lists (which we don't want)
and requires to tag and untag the data in the list.

That's why we change it into an alternative representation
```

data TermCon : Set where
  integer    : ℤ → TermCon
  bytestring : ByteString → TermCon
  string     : String → TermCon
  bool       : Bool → TermCon
  unit       : TermCon
  pdata      : DATA → TermCon
  pair       : TermCon → TermCon → TermCon
  list       : TyTag → List TermCon → TermCon

{-# FOREIGN GHC import PlutusCore                       #-}
{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC TermCon = data TermCon (TmInteger | TmByteString | TmString | TmBool | TmUnit | TmData | TmPair | TmList) #-}

getTag : TermCon → TyTag
getTag (integer x) = integer
getTag (bytestring x) = bytestring
getTag (string x) = string
getTag (bool x) = bool
getTag unit = unit
getTag (pdata x) = pdata
getTag (pair x y) = pair (getTag x) (getTag y)
getTag (list t _) = list t

data Untyped : Set where
  UVar : ℕ → Untyped
  ULambda : Untyped → Untyped
  UApp : Untyped → Untyped → Untyped
  UCon : TermCon → Untyped
  UError : Untyped
  UBuiltin : Builtin → Untyped
  UDelay : Untyped → Untyped
  UForce : Untyped → Untyped

{-# FOREIGN GHC import Untyped #-}
{-# COMPILE GHC Untyped = data UTerm (UVar | ULambda  | UApp | UCon | UError | UBuiltin | UDelay | UForce) #-}
```

```
data TmCon : Set where 
  tmcon : (t : TyTag) → ⟦ t ⟧tag → TmCon

termCon2TmCon : TermCon → Maybe TmCon
listTermCon2TmCon : TyTag → List TermCon → Maybe TmCon

termCon2TmCon (integer x) = return (tmcon integer x)
termCon2TmCon (bytestring x) = return (tmcon bytestring x)
termCon2TmCon (string x) = return (tmcon string x)
termCon2TmCon (bool x) = return (tmcon bool x)
termCon2TmCon unit = return (tmcon unit tt)
termCon2TmCon (pdata x) = return (tmcon pdata x)
termCon2TmCon (pair x y) = do 
        (tmcon tx x) ← termCon2TmCon x 
        (tmcon ty y) ← termCon2TmCon y 
        return ( tmcon (pair tx ty) (x , y))
termCon2TmCon (list t xs) = listTermCon2TmCon t xs

listTermCon2TmCon t [] = return (tmcon (list t) [])
listTermCon2TmCon t (x ∷ xs) with termCon2TmCon x  
... | nothing  = nothing
... | just (tmcon tx x') with listTermCon2TmCon t xs 
...      | nothing = nothing
...      | just (tmcon (list ts) xs') with decTag tx ts 
...         | yes refl = just (tmcon (list ts) (x' ∷ xs'))
...         | no _     = nothing 
listTermCon2TmCon t (x ∷ xs) | just (tmcon tx x') | just _ = nothing

{-
tmCon2TermCon : TmCon → TermCon
listTmCon2TermCon : (t : TyTag) → List (⟦ t ⟧tag) → List TermCon

tmCon2TermCon (tmcon integer x) = integer x
tmCon2TermCon (tmcon bytestring x) = bytestring x
tmCon2TermCon (tmcon string x) = string x
tmCon2TermCon (tmcon bool x) = bool x
tmCon2TermCon (tmcon unit x) = unit
tmCon2TermCon (tmcon pdata x) = pdata x
tmCon2TermCon (tmcon (pair t t₁) (x , y)) = pair (tmCon2TermCon (tmcon t x)) (tmCon2TermCon (tmcon t₁ y))
tmCon2TermCon (tmcon (list t) xs) = list (list t) (listTmCon2TermCon t xs)

listTmCon2TermCon t [] = []
listTmCon2TermCon t (x ∷ xs) = tmCon2TermCon (tmcon t x) ∷ listTmCon2TermCon t xs 
-}
```