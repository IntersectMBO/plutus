---
title: Builtin.ByteString.Properties
layout: page
---

This module collects the proofs of the laws of the bytestring builtins defined
in `Builtin.ByteString.Denotation`. Together they prove every property in the
Haskell property test suites for the bitwise and conversion builtins:

| Haskell test suite                        | Agda module                                  |
|-------------------------------------------|----------------------------------------------|
| `Evaluation.Builtins.Bitwise.CIP0122`     | `Builtin.ByteString.Properties.Logical`      |
| `Evaluation.Builtins.Bitwise.CIP0123`     | `Builtin.ByteString.Properties.ShiftRotate`, |
|                                           | `Builtin.ByteString.Properties.Count`        |
| `Evaluation.Builtins.Conversion` (CIP-121)| `Builtin.ByteString.Properties.Conversion`   |

The Haskell tests check the laws on random inputs of bounded size; here they
are proved for all inputs. Where a test fixes one of the two semantics of the
logical operations (padding or truncation) and the law holds for both, it is
proved for both. The laws are stated on the denotations, which are what the
CEK machines execute, and the hypotheses spell out the input ranges in which
the builtins succeed (shift and rotation amounts that fit in a 64-bit `Int`,
outputs of at most 8192 bytes).

The proofs rest on two supporting modules:

* `Builtin.ByteString.Properties.Byte`: laws of single bytes, lifted bit by bit
  from the laws of booleans, and a decision procedure for statements about all
  256 bytes;
* `Builtin.ByteString.Properties.Base`: lengths, the bit view of a bytestring
  (`toBits` and `fromBits` are mutually inverse), and `readBit`/`writeBits` as
  lookups and updates of the bit view.

```
module Builtin.ByteString.Properties where

open import Builtin.ByteString.Properties.Byte public
open import Builtin.ByteString.Properties.Base public
open import Builtin.ByteString.Properties.Logical public
open import Builtin.ByteString.Properties.ShiftRotate public
open import Builtin.ByteString.Properties.Count public
open import Builtin.ByteString.Properties.Conversion public
```
