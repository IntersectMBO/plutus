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
open import Builtin.Constant.AtomicType
```

Type constants are either atomic, or pair, or lists.

```
data TyCon (Φ : Con) : Set where
  atomic     : AtomicTyCon → TyCon Φ
  list       : Ty Φ → TyCon Φ
  pair       : Ty Φ → Ty Φ → TyCon Φ

pattern integer = atomic aInteger
pattern bytestring = atomic aBytestring
pattern string = atomic aString
pattern unit = atomic aUnit
pattern bool = atomic aBool
pattern pdata = atomic aData
pattern bls12-381-g1-element = atomic aBls12-381-g1-element
pattern bls12-381-g2-element = atomic aBls12-381-g2-element 
pattern bls12-381-mlresult   = atomic aBls12-381-mlresult

```


