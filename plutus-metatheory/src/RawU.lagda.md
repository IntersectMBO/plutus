
```
module RawU where
```
## Imports

```
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Bool using (Bool)
open import Utils using (ByteString;DATA;List)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes;no;¬_)

open import Builtin using (Builtin)
open Builtin.Builtin

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

{-# FOREIGN GHC type TyTag = DefaultUni ????? #-}
{-# FOREIGN GHC pattern TagInt        = DefaultUniInteger  #-}
{-# FOREIGN GHC pattern TagBS         = DefaultUniByteString #-}
{-# FOREIGN GHC pattern TagStr        = DefaultUniString #-}
{-# FOREIGN GHC pattern TagBool       = DefaultUniBool #-}
{-# FOREIGN GHC pattern TagUnit       = DefaultUniUnit #-}
{-# FOREIGN GHC pattern TagData       = DefaultUniData #-}
{-# FOREIGN GHC pattern TagPair ta tb = DefaultUniPair ta tb #-}
{-# FOREIGN GHC pattern TagList ta    = DefaultUniList ta #-}
{-# COMPILE GHC TyTag = data TyTag (TagInt | TagBS | TagStr | TagBool | TagUnit | TagData | TagPair | TagList) #-}
```
## Raw syntax

This version is not intrinsically well-scoped. It's an easy to work
with rendering of the untyped plutus-core syntax.

```

data TermCon : Set where
  integer    : ℤ → TermCon
  bytestring : ByteString → TermCon
  string     : String → TermCon
  bool       : Bool → TermCon
  unit       : TermCon
  pdata      : DATA → TermCon
  pair       : TyTag → TyTag → TermCon → TermCon → TermCon
  list       : TyTag → List TermCon → TermCon

{-# FOREIGN GHC import PlutusCore                       #-}
{-# FOREIGN GHC import Raw #-}
{-# FOREIGN GHC type TermCon = Some (ValueOf DefaultUni) #-}
{-# FOREIGN GHC pattern TmInteger      i = Some (ValueOf DefaultUniInteger i) #-}
{-# FOREIGN GHC pattern TmByteString   b = Some (ValueOf DefaultUniByteString b) #-}
{-# FOREIGN GHC pattern TmString       s = Some (ValueOf DefaultUniString s) #-}
{-# FOREIGN GHC pattern TmUnit           = Some (ValueOf DefaultUniUnit ()) #-}
{-# FOREIGN GHC pattern TmBool         b = Some (ValueOf DefaultUniBool b) #-}
{-# FOREIGN GHC pattern TmData         d = Some (ValueOf DefaultUniData d) #-}
{-# FOREIGN GHC pattern TmPair ta tb a b = Some (ValueOf (DefaultUniPair ta tb) (a,b)) #-}
{-# FOREIGN GHC pattern TmList ta  xs  = Some (ValueOf (DefaultUniList ta) xs) #-}
{-# COMPILE GHC TermCon = data TermCon (TmInteger | TmByteString | TmString | TmBool | TmUnit | TmData | TmPair | TmList) #-}

getTag : TermCon → TyTag
getTag (integer x) = integer
getTag (bytestring x) = bytestring
getTag (string x) = string
getTag (bool x) = bool
getTag unit = unit
getTag (pdata x) = pdata
getTag (pair t t' _ _) = pair t t'
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