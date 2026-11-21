---
title: Builtin.Value.Data.Properties
layout: page
---

This module proves that the encoding of values as `Data` and the decoding are inverse:
decoding the encoding of a value gives it back, and data that decodes to a value is its
encoding.

```
module Builtin.Value.Data.Properties where
```

## Imports

```
open import Data.List using (_∷_; [])
open import Data.Maybe using (just; nothing; _>>=_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

import Data.List as List
import Builtin.Data as D

open import Builtin.Value.Base
open import Builtin.Value.Data
open import Builtin.Value.Nested
open import Builtin.Value.Nested.Properties
```

## Decoding inverts encoding

```
decodeTokens-encodeTokens : ∀ ts → decodeTokens (encodeTokens ts) ≡ just ts
decodeTokens-encodeTokens []             = refl
decodeTokens-encodeTokens ((t , q) ∷ ts)
  rewrite decodeTokens-encodeTokens ts = refl

decodeNested-encode : ∀ ns → decodeNested (List.map encodeCurrency ns) ≡ just ns
decodeNested-encode []              = refl
decodeNested-encode ((c , ts) ∷ ns)
  rewrite decodeTokens-encodeTokens ts | decodeNested-encode ns = refl
```

The encoding of a value is that of the grouping of its entries, from which `toValue∞`
recovers the value (see `Builtin.Value.Nested.Properties`).

```
unValueData∞-valueData∞ : ∀ v → unValueData∞ (valueData∞ v) ≡ just v
unValueData∞-valueData∞ v =
  trans (cong (_>>= toValue∞) (decodeNested-encode (toNested∞ v)))
        (toValue∞-toNested∞ v)
```

## Encoding inverts decoding

```
encodeTokens-decodeTokens
  : ∀ ps {ts} → decodeTokens ps ≡ just ts → encodeTokens ts ≡ ps
encodeTokens-decodeTokens [] refl = refl
encodeTokens-decodeTokens ((t , q) ∷ ps) eq
  with D.unBData t in et | D.unIData q in eq' | decodeTokens ps in ets
encodeTokens-decodeTokens ((t , q) ∷ ps) refl | just _ | just _ | just _ =
  cong₂ _∷_
    (cong₂ _,_ (sym (D.unBData-just et)) (sym (D.unIData-just eq')))
    (encodeTokens-decodeTokens ps ets)
encodeTokens-decodeTokens ((t , q) ∷ ps) () | nothing | _       | _
encodeTokens-decodeTokens ((t , q) ∷ ps) () | just _  | nothing | _
encodeTokens-decodeTokens ((t , q) ∷ ps) () | just _  | just _  | nothing

encode-decodeNested
  : ∀ ps {ns} → decodeNested ps ≡ just ns → List.map encodeCurrency ns ≡ ps
encode-decodeNested [] refl = refl
encode-decodeNested ((c , ts) ∷ ps) eq
  with D.unBData c in ec | D.unMapData ts in em
... | just _ | just pts with decodeTokens pts in edt | decodeNested ps in ens
encode-decodeNested ((c , ts) ∷ ps) refl | just _ | just pts | just _ | just _ =
  cong₂ _∷_
    (cong₂ _,_
      (sym (D.unBData-just ec))
      (trans (cong D.Map (encodeTokens-decodeTokens pts edt))
             (sym (D.unMapData-just em))))
    (encode-decodeNested ps ens)
encode-decodeNested ((c , ts) ∷ ps) () | just _ | just _ | nothing | _
encode-decodeNested ((c , ts) ∷ ps) () | just _ | just _ | just _  | nothing
encode-decodeNested ((c , ts) ∷ ps) () | nothing | _
encode-decodeNested ((c , ts) ∷ ps) () | just _  | nothing
```

Data that decodes to a value is its encoding, so the encoding of values is canonical:
every value has exactly one encoding that decodes to it.

```
valueData∞-unValueData∞ : ∀ d {v} → unValueData∞ d ≡ just v → valueData∞ v ≡ d
valueData∞-unValueData∞ d eq with D.unMapData d in em
... | just ps with decodeNested ps in edn
...   | just ns =
  trans (cong encodeNested (toNested∞-toValue∞ ns eq))
        (trans (cong D.Map (encode-decodeNested ps edn)) (sym (D.unMapData-just em)))
valueData∞-unValueData∞ d () | just _ | nothing
valueData∞-unValueData∞ d () | nothing
```
