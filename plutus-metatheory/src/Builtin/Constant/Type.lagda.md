---
title: Type level constants
layout: page
---

This module contains the type level constants and also postulated
operations for builtins that are imported from Haskell libraries.

The postulated operations are in this module because it is not
parameterised. They could also be placed elsewhere.

```
module Builtin.Constant.Type
  (Con : Set)(Ty : Con → Set) where
```

## Imports

```
open import Agda.Builtin.Char
open import Agda.Builtin.Int
open import Agda.Builtin.String
open import Data.Integer using (ℤ;-_;+≤+;-≤+;-≤-;_<_;_>_;_≤?_;_<?_;_≥_;_≤_)
open import Data.Unit using (⊤)
open import Data.Bool using (Bool)
open import Data.Product
open import Relation.Binary
open import Data.Nat using (ℕ;_*_;z≤n;s≤s;zero;suc)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Function

open import Utils
```

## Type constants

We have six base types referred to as type constants:

```
data TyCon (Φ : Con) : Set where
  integer    : TyCon Φ
  bytestring : TyCon Φ
  string     : TyCon Φ
  unit       : TyCon Φ
  bool       : TyCon Φ
  list       : Ty Φ → TyCon Φ
  pair       : Ty Φ → Ty Φ → TyCon Φ
  Data       : TyCon Φ


--{-# FOREIGN GHC {-# LANGUAGE GADTs, PatternSynonyms #-}                #-}
--{-# FOREIGN GHC import PlutusCore                                      #-}
--{-# FOREIGN GHC type TypeBuiltin = SomeTypeIn DefaultUni               #-}
--{-# FOREIGN GHC pattern TyInteger    = SomeTypeIn DefaultUniInteger    #-}
--{-# FOREIGN GHC pattern TyByteString = SomeTypeIn DefaultUniByteString #-}
--{-# FOREIGN GHC pattern TyString     = SomeTypeIn DefaultUniString     #-}
--{-# FOREIGN GHC pattern TyUnit       = SomeTypeIn DefaultUniUnit       #-}
--{-# FOREIGN GHC pattern TyBool       = SomeTypeIn DefaultUniBool       #-}
--{-# FOREIGN GHC pattern TyList a     = SomeTypeIn DefaultUniList a     #-}
--{-# FOREIGN GHC pattern TyPair a b   = SomeTypeIn DefaultUniPair a b   #-}
--{-# FOREIGN GHC pattern TyData       = SomeTypeIn DefaultUniData       #-}
--{-# COMPILE GHC TyCon = data TypeBuiltin (TyInteger | TyByteString | TyString | TyUnit | TyBool | TyList | TyPair | TyData) #-}
```
