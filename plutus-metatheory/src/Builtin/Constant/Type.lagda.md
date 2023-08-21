---
title: Type level constants
layout: page
---

This module contains the type level constants and also postulated
operations for builtins that are imported from Haskell libraries.

The postulated operations are in this module because it is not
parameterised. They could also be placed elsewhere.

```
module Builtin.Constant.Type where
```

## Imports

```
open import Utils using (Kind;♯;_⇒_)
open import Builtin.Constant.AtomicType public
```

Type constants are either atomic, or pair, or lists.
They are indexed by Kind. 

The use of higher-order constants like list and pair,
means that we do not have to define renaming and substitution 
for type constants, since the construction of a list applied to 
some type uses the ordinary type application machinery.

The use of kind ♯ limits the types for which we can construct lists and pairs.

```
data TyCon : Kind → Set where
  atomic     : AtomicTyCon → TyCon ♯
  list       : TyCon (♯ ⇒ ♯)
  pair       : TyCon (♯ ⇒ (♯ ⇒ ♯))
```
