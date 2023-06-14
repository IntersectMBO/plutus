---
title: Type level constants
layout: page
---

This module contains the type level constants and also postulated
operations for builtins that are imported from Haskell libraries.

The postulated operations are in this module because it is not
parameterised. They could also be placed elsewhere.

```
{-# OPTIONS --type-in-type #-}

module Builtin.Constant.Type where
```

## Imports

```
open import Utils using (Kind;♯;_⇒_)
open import Builtin.Constant.AtomicType public
```

Type constants are either atomic, or pair, or lists.

```
data TyCon : Kind → Set where
  atomic     : AtomicTyCon → TyCon ♯
  list       : TyCon (♯ ⇒ ♯)
  pair       : TyCon (♯ ⇒ (♯ ⇒ ♯))
```
