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
-- no imports
```

## Type constants

We have twelve base types referred to as type constants:

```
data TyCon (Φ : Con) : Set where
  integer              : TyCon Φ
  bytestring           : TyCon Φ
  string               : TyCon Φ
  unit                 : TyCon Φ
  bool                 : TyCon Φ
  list                 : Ty Φ → TyCon Φ
  pair                 : Ty Φ → Ty Φ → TyCon Φ
  pdata                : TyCon Φ
  bls12-381-g1-element : TyCon Φ
  bls12-381-g2-element : TyCon Φ
  bls12-381-mlresult   : TyCon Φ
```
