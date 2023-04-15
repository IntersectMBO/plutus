
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

open import Builtin using (Builtin)
open Builtin.Builtin
```
## Raw syntax

This version is not intrinsically well-scoped. It's an easy to work
with rendering of the untyped plutus-core syntax.

```
{-
open import Builtin.Signature using (_⊢♯)

TyTag : Set
TyTag = 0 ⊢♯
-}
data TermCon : Set where
  integer    : ℤ → TermCon
  bytestring : ByteString → TermCon
  string     : String → TermCon
  bool       : Bool → TermCon
  unit       : TermCon
  pdata      : DATA → TermCon
  pair       : TermCon → TermCon → TermCon
  list       : List TermCon → TermCon

{-# FOREIGN GHC import Raw #-}
{-# FOREIGN GHC type TermCon = Some (ValueOf DefaultUni) #-}
{-# FOREIGN GHC pattern TmInteger    i = Some (ValueOf DefaultUniInteger i) #-}
{-# FOREIGN GHC pattern TmByteString b = Some (ValueOf DefaultUniByteString b) #-}
{-# FOREIGN GHC pattern TmString     s = Some (ValueOf DefaultUniString s) #-}
{-# FOREIGN GHC pattern TmUnit         = Some (ValueOf DefaultUniUnit ()) #-}
{-# FOREIGN GHC pattern TmBool       b = Some (ValueOf DefaultUniBool b) #-}
{-# FOREIGN GHC pattern TmData       d = Some (ValueOf DefaultUniData d) #-}
{-# FOREIGN GHC pattern TmPair a b = Some (ValueOf (DefaultUniPair DefaultUniData DefaultUniData) (a,b)) #-}
{-# FOREIGN GHC pattern TmList  xs = Some (ValueOf (DefaultUniList DefaultUniData) xs) #-}
{-# COMPILE GHC TermCon = data TermCon (TmInteger | TmByteString | TmString | TmBool | TmUnit | TmData | TmPair | TmList) #-}

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