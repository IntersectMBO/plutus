---
title: Builtin.Value.Data
layout: page
---

This module encodes values as `Data`, and decodes them from it. The builtins
`valueData` and `unValueData`, which also impose the bounds of the builtin type, are
defined from these in `Builtin.Value`.

```
module Builtin.Value.Data where
```

## Imports

```
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; _>>=_)
open import Data.Product using (_×_; _,_)
open import Function.Base using (_∘_)

import Data.List as List
import Builtin.Data as D

open import Builtin.Value.Base
open import Builtin.Value.Nested
```

## Encoding

`valueData∞ v` encodes `v` as a map from each currency symbol, as a bytestring, to the
map from each of its tokens, as a bytestring, to its quantity, as an integer. Both maps
are sorted by their keys, and no currency has an empty map of tokens.

```
encodeTokens : Tokens → List (D.Data × D.Data)
encodeTokens = List.map λ (t , q) → D.B t , D.I q

encodeCurrency : CurrencySymbol × Tokens → D.Data × D.Data
encodeCurrency (c , ts) = D.B c , D.Map (encodeTokens ts)

encodeNested : Nested → D.Data
encodeNested ns = D.Map (List.map encodeCurrency ns)

valueData∞ : Value∞ → D.Data
valueData∞ = encodeNested ∘ toNested∞
```

## Decoding

`unValueData∞ d` decodes a value encoded as by `valueData∞`. It fails unless `d` is a
map from bytestrings to maps from bytestrings to integers, which is well-formed (see
`Builtin.Value.Nested`): there are no repeated or unsorted currency symbols or token
names, and no currency without tokens. It also fails if a quantity is zero.

```
decodeTokens : List (D.Data × D.Data) → Maybe Tokens
decodeTokens []             = just []
decodeTokens ((t , q) ∷ ps) = do
  t' ← D.unBData t
  q' ← D.unIData q
  ts ← decodeTokens ps
  just ((t' , q') ∷ ts)

decodeNested : List (D.Data × D.Data) → Maybe Nested
decodeNested []              = just []
decodeNested ((c , ts) ∷ ps) = do
  c'  ← D.unBData c
  ts' ← D.unMapData ts >>= decodeTokens
  ns  ← decodeNested ps
  just ((c' , ts') ∷ ns)

unValueData∞ : D.Data → Maybe Value∞
unValueData∞ d = D.unMapData d >>= decodeNested >>= toValue∞
```
