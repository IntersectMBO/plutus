---
title: Conformance.Builtin.Parser.Data
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/parser/data`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Parser.Data where

open import Conformance.Eval
```

## dataByteString

```
-- builtin/parser/data/dataByteString
test-dataByteString : Untyped
test-dataByteString = (UCon (tagCon pdata (bDATA (mkByteString "\SOH#Eg\137\171\205\239"))))

expected-dataByteString : Result
expected-dataByteString = success (UCon (tagCon pdata (bDATA (mkByteString "\SOH#Eg\137\171\205\239"))))

-- Pending: bytestring inside a `data` constant.
pending-dataByteString : Set
pending-dataByteString = Pending (evalRaw test-dataByteString ≡ expected-dataByteString)
```

## dataConstr

```
-- builtin/parser/data/dataConstr
test-dataConstr : Untyped
test-dataConstr = (UCon (tagCon pdata (ConstrDATA (ℤ.pos 1) ((iDATA (ℤ.pos 1)) ∷ []))))

expected-dataConstr : Result
expected-dataConstr = success (UCon (tagCon pdata (ConstrDATA (ℤ.pos 1) ((iDATA (ℤ.pos 1)) ∷ []))))

_ : evalRaw test-dataConstr ≡ expected-dataConstr
_ = refl
```

## dataInteger

```
-- builtin/parser/data/dataInteger
test-dataInteger : Untyped
test-dataInteger = (UCon (tagCon pdata (iDATA (ℤ.pos 12354898))))

expected-dataInteger : Result
expected-dataInteger = success (UCon (tagCon pdata (iDATA (ℤ.pos 12354898))))

_ : evalRaw test-dataInteger ≡ expected-dataInteger
_ = refl
```

## dataList

```
-- builtin/parser/data/dataList
test-dataList : Untyped
test-dataList = (UCon (tagCon pdata (ListDATA ((ConstrDATA (ℤ.pos 1) ([])) ∷ (iDATA (ℤ.pos 1234)) ∷ (bDATA (mkByteString "\171\205\239")) ∷ []))))

expected-dataList : Result
expected-dataList = success (UCon (tagCon pdata (ListDATA ((ConstrDATA (ℤ.pos 1) ([])) ∷ (iDATA (ℤ.pos 1234)) ∷ (bDATA (mkByteString "\171\205\239")) ∷ []))))

-- Pending: bytestring inside a `data` constant.
pending-dataList : Set
pending-dataList = Pending (evalRaw test-dataList ≡ expected-dataList)
```

## dataMap

```
-- builtin/parser/data/dataMap
test-dataMap : Untyped
test-dataMap = (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\SOH#")) , (iDATA (ℤ.pos 12345))) ∷ ((iDATA (ℤ.pos 789453)) , (bDATA (mkByteString "Eg\137"))) ∷ ((ListDATA ((iDATA (ℤ.negsuc 12364689485)) ∷ [])) , (ConstrDATA (ℤ.pos 7) ([]))) ∷ []))))

expected-dataMap : Result
expected-dataMap = success (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\SOH#")) , (iDATA (ℤ.pos 12345))) ∷ ((iDATA (ℤ.pos 789453)) , (bDATA (mkByteString "Eg\137"))) ∷ ((ListDATA ((iDATA (ℤ.negsuc 12364689485)) ∷ [])) , (ConstrDATA (ℤ.pos 7) ([]))) ∷ []))))

-- Pending: bytestring inside a `data` constant.
pending-dataMap : Set
pending-dataMap = Pending (evalRaw test-dataMap ≡ expected-dataMap)
```

## dataMisByteString

Skipped: the program does not parse or has free variables (`parse/decode error`).

## dataMisConstr

Skipped: the program does not parse or has free variables (`parse/decode error`).

## dataMisInteger

Skipped: the program does not parse or has free variables (`parse/decode error`).

## dataMisList

Skipped: the program does not parse or has free variables (`parse/decode error`).

## dataMisMap

Skipped: the program does not parse or has free variables (`parse/decode error`).
