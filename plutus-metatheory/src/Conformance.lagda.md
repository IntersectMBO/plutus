---
title: Conformance
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Unit tests generated from the UPLC evaluation conformance test cases in
`plutus-conformance/test-cases/uplc/evaluation`. Each case is a `refl` proof
that the untyped CEK machine (`Untyped.CEK`) produces the expected result, or a
pending statement of that proposition when the case involves constants or
builtins that are still postulated on the Agda side. See `Conformance.Eval`.

| | cases |
|---|---|
| proved by `refl` | 228 |
| pending (postulated constants or builtins, or known failures) | 711 |
| skipped: constant not expressible in Agda | 6 |
| skipped: program does not parse | 64 |

```
module Conformance where

import Conformance.Eval
import Conformance.Builtin.Interleaving
import Conformance.Builtin.Parser.Array
import Conformance.Builtin.Parser.Bls12381.G1
import Conformance.Builtin.Parser.Bls12381.G2
import Conformance.Builtin.Parser.Bool
import Conformance.Builtin.Parser.Bytestring
import Conformance.Builtin.Parser.Data
import Conformance.Builtin.Parser.Integer
import Conformance.Builtin.Parser.List
import Conformance.Builtin.Parser.Pair
import Conformance.Builtin.Parser.String
import Conformance.Builtin.Parser.Unit
import Conformance.Builtin.Parser.Value
import Conformance.Builtin.Semantics
import Conformance.Builtin.Semantics.AddInteger
import Conformance.Builtin.Semantics.AndByteString
import Conformance.Builtin.Semantics.AppendByteString
import Conformance.Builtin.Semantics.Blake2b224
import Conformance.Builtin.Semantics.Blake2b256
import Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G1.Arith
import Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G1.Uncompress
import Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G2.Arith
import Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G2.Uncompress
import Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.Pairing
import Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.Signature
import Conformance.Builtin.Semantics.Bls12381G1Add
import Conformance.Builtin.Semantics.Bls12381G1Compress
import Conformance.Builtin.Semantics.Bls12381G1Equal
import Conformance.Builtin.Semantics.Bls12381G1HashToGroup
import Conformance.Builtin.Semantics.Bls12381G1MultiScalarMul
import Conformance.Builtin.Semantics.Bls12381G1Neg
import Conformance.Builtin.Semantics.Bls12381G1ScalarMul
import Conformance.Builtin.Semantics.Bls12381G1Uncompress
import Conformance.Builtin.Semantics.Bls12381G2Add
import Conformance.Builtin.Semantics.Bls12381G2Compress
import Conformance.Builtin.Semantics.Bls12381G2Equal
import Conformance.Builtin.Semantics.Bls12381G2HashToGroup
import Conformance.Builtin.Semantics.Bls12381G2MultiScalarMul
import Conformance.Builtin.Semantics.Bls12381G2Neg
import Conformance.Builtin.Semantics.Bls12381G2ScalarMul
import Conformance.Builtin.Semantics.Bls12381G2Uncompress
import Conformance.Builtin.Semantics.Bls12381MillerLoop
import Conformance.Builtin.Semantics.ByteStringToInteger
import Conformance.Builtin.Semantics.ByteStringToInteger.BigEndian
import Conformance.Builtin.Semantics.ByteStringToInteger.LittleEndian
import Conformance.Builtin.Semantics.ChooseList
import Conformance.Builtin.Semantics.ChooseUnit
import Conformance.Builtin.Semantics.ComplementByteString
import Conformance.Builtin.Semantics.ConsByteString
import Conformance.Builtin.Semantics.CountSetBits
import Conformance.Builtin.Semantics.DecodeUtf8
import Conformance.Builtin.Semantics.DivideInteger
import Conformance.Builtin.Semantics.DropList
import Conformance.Builtin.Semantics.EqualsByteString
import Conformance.Builtin.Semantics.EqualsData
import Conformance.Builtin.Semantics.EqualsInteger
import Conformance.Builtin.Semantics.EqualsString
import Conformance.Builtin.Semantics.ExpModInteger
import Conformance.Builtin.Semantics.ExpModInteger.Extra
import Conformance.Builtin.Semantics.FindFirstSetBit
import Conformance.Builtin.Semantics.HeadList
import Conformance.Builtin.Semantics.IfThenElse
import Conformance.Builtin.Semantics.IndexArray
import Conformance.Builtin.Semantics.IndexByteString
import Conformance.Builtin.Semantics.InsertCoin
import Conformance.Builtin.Semantics.IntegerToByteString.BigEndian.Bounded
import Conformance.Builtin.Semantics.IntegerToByteString.BigEndian.Unbounded
import Conformance.Builtin.Semantics.IntegerToByteString.LittleEndian.Bounded
import Conformance.Builtin.Semantics.IntegerToByteString.LittleEndian.Unbounded
import Conformance.Builtin.Semantics.Keccak256
import Conformance.Builtin.Semantics.LengthOfArray
import Conformance.Builtin.Semantics.LessThanByteString
import Conformance.Builtin.Semantics.LessThanEqualsByteString
import Conformance.Builtin.Semantics.LessThanEqualsInteger
import Conformance.Builtin.Semantics.LessThanInteger
import Conformance.Builtin.Semantics.ListToArray
import Conformance.Builtin.Semantics.LookupCoin
import Conformance.Builtin.Semantics.MkCons
import Conformance.Builtin.Semantics.ModInteger
import Conformance.Builtin.Semantics.MultiplyInteger
import Conformance.Builtin.Semantics.NullList
import Conformance.Builtin.Semantics.OrByteString
import Conformance.Builtin.Semantics.QuotientInteger
import Conformance.Builtin.Semantics.ReadBit
import Conformance.Builtin.Semantics.RemainderInteger
import Conformance.Builtin.Semantics.ReplicateByte
import Conformance.Builtin.Semantics.Ripemd160
import Conformance.Builtin.Semantics.RotateByteString
import Conformance.Builtin.Semantics.ScaleValue
import Conformance.Builtin.Semantics.Sha2256
import Conformance.Builtin.Semantics.Sha3256
import Conformance.Builtin.Semantics.ShiftByteString
import Conformance.Builtin.Semantics.SliceByteString
import Conformance.Builtin.Semantics.SubtractInteger
import Conformance.Builtin.Semantics.TailList
import Conformance.Builtin.Semantics.UnBData
import Conformance.Builtin.Semantics.UnConstrData
import Conformance.Builtin.Semantics.UnIData
import Conformance.Builtin.Semantics.UnListData
import Conformance.Builtin.Semantics.UnMapData
import Conformance.Builtin.Semantics.UnValueData
import Conformance.Builtin.Semantics.UnionValue
import Conformance.Builtin.Semantics.ValueContains
import Conformance.Builtin.Semantics.ValueData
import Conformance.Builtin.Semantics.VerifyEcdsaSecp256k1Signature
import Conformance.Builtin.Semantics.VerifyEd25519Signature
import Conformance.Builtin.Semantics.VerifySchnorrSecp256k1Signature
import Conformance.Builtin.Semantics.WriteBits
import Conformance.Builtin.Semantics.XorByteString
import Conformance.Example
import Conformance.Term
import Conformance.Term.App
import Conformance.Term.Case
import Conformance.Term.ConstantCase.Bool
import Conformance.Term.ConstantCase.Data
import Conformance.Term.ConstantCase.Integer
import Conformance.Term.ConstantCase.List
import Conformance.Term.ConstantCase.Pair
import Conformance.Term.ConstantCase.Unit
import Conformance.Term.Constr
import Conformance.Term.Delay
import Conformance.Term.Force
import Conformance.Term.Lam
import Conformance.Term.Parser.Constr
```
