---
title: Builtin.ByteString
layout: page
---

```
module Builtin.ByteString where
```

## Imports

```
open import Builtin.ByteString.Base
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Integer using (ℤ; +_)
open import Data.Nat using (ℕ; _^_)
open import Relation.Nullary.Decidable using (yes; no)
open import Data.Bool using (Bool; true; false)
open import Function.Base using (_∘_; _$_)

import Data.Nat.Properties as ℕ
import Data.Integer as ℤ
import Builtin.Integer.Base as ℤ
```

## Cardano Builtin Functions on ByteString

```
appendByteString : ByteString → ByteString → ByteString
appendByteString = _++_

consByteStringV2 : ℤ → ByteString → Maybe ByteString
consByteStringV2 (ℤ.pos n) bs with n ℕ.<? 2 ^ 8
... | yes p = just (natToByte n p ∷ bs)
... | no _ = nothing
consByteStringV2 (ℤ.negsuc n) _ = nothing

sliceByteString : ℤ → ℤ → ByteString → ByteString
sliceByteString start subStrLen bs =
  take (clamp subStrLen) (drop (clamp start) bs)
  where
    clamp : ℤ → ℕ
    clamp (ℤ.pos n)    = n
    clamp (ℤ.negsuc _) = 0

lengthOfByteString : ByteString → ℤ
lengthOfByteString = (+_) ∘ length

indexByteString : ℤ → ByteString → Maybe Byte
indexByteString (ℤ.pos i)    bs = index i bs
indexByteString (ℤ.negsuc _) _  = nothing
```