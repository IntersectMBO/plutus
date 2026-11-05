---
title: Builtin.Array.Base
layout: page
---

```
module Builtin.Array.Base where

open import Data.List
open import Data.Nat using (ℕ; _<?_)
open import Data.Integer using (ℤ; -[1+_]; +_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Fin using (fromℕ<; zero; suc)
open import Relation.Nullary using (yes; no)
```

## Semantics of arrays

The denotation of the array type is identical to that of lists, but we expect
that in practice arrays will be implemented in such a way that the
`lengthOfArray` and `indexArray` functions will be constant time and listToArray
may be nontrivial, requiring linear time.

```
Array : Set → Set
Array = List

private variable
  A : Set
```

## Built-in functions on Array

### Batch 6

```
lengthOfArray : Array A → ℤ
lengthOfArray xs = + (length xs)

listToArray : List A → Array A
listToArray xs = xs

indexArray : Array A → ℤ → Maybe A
indexArray xs (-[1+ n ]) = nothing
indexArray xs (+ n)
  with n <? length xs
... | yes n<len = just (lookup xs (fromℕ< n<len))
... | no _ = nothing
```

### Batch 7

Indices are zero-based.

```
multiIndexArray : Array A → List ℤ → Maybe (List A)
multiIndexArray _  [] = just []
multiIndexArray xs (i ∷ is)
  with indexArray xs i
... | nothing = nothing
... | just y
  with multiIndexArray xs is
... | nothing = nothing
... | just ys = just (y ∷ ys)
```

