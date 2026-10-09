---
title: Conformance.Builtin.Semantics
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics where

open import Conformance.Eval
```

## appendString

```
-- builtin/semantics/appendString
test-appendString : Untyped
test-appendString = (UApp (UApp (UBuiltin appendString) (UCon (tagCon string "Ola"))) (UCon (tagCon string " mundo!")))

expected-appendString : Result
expected-appendString = success (UCon (tagCon string "Ola mundo!"))

_ : evalRaw test-appendString ≡ expected-appendString
_ = refl
```

## bData

```
-- builtin/semantics/bData
test-bData : Untyped
test-bData = (UApp (UBuiltin bData) (UCon (tagCon bytestring (mkByteString "\n\253"))))

expected-bData : Result
expected-bData = success (UCon (tagCon pdata (bDATA (mkByteString "\n\253"))))

-- Pending: bytestring constant; bytestring inside a `data` constant.
pending-bData : Set
pending-bData = Pending (evalRaw test-bData ≡ expected-bData)
```

## chooseDataByteString

```
-- builtin/semantics/chooseDataByteString
test-chooseDataByteString : Untyped
test-chooseDataByteString = (UApp (UApp (UApp (UApp (UApp (UApp (UForce (UBuiltin chooseData)) (UCon (tagCon pdata (bDATA (mkByteString "\NUL\SUB"))))) (ULambda (UCon (tagCon integer (ℤ.pos 1))))) (ULambda (UCon (tagCon string "two")))) (ULambda (UVar 0))) (ULambda (UCon (tagCon pdata (iDATA (ℤ.pos 4)))))) (ULambda (UCon (tagCon pdata (bDATA (mkByteString "\ENQ"))))))

expected-chooseDataByteString : Result
expected-chooseDataByteString = success (ULambda (UCon (tagCon pdata (bDATA (mkByteString "\ENQ")))))

-- Pending: bytestring inside a `data` constant.
pending-chooseDataByteString : Set
pending-chooseDataByteString = Pending (evalRaw test-chooseDataByteString ≡ expected-chooseDataByteString)
```

## chooseDataConstr

```
-- builtin/semantics/chooseDataConstr
test-chooseDataConstr : Untyped
test-chooseDataConstr = (UApp (UApp (UApp (UApp (UApp (UApp (UForce (UBuiltin chooseData)) (UCon (tagCon pdata (ConstrDATA (ℤ.pos 1) ((iDATA (ℤ.pos 1)) ∷ []))))) (ULambda (UCon (tagCon integer (ℤ.pos 1))))) (ULambda (UCon (tagCon string "two")))) (ULambda (UVar 0))) (ULambda (UCon (tagCon pdata (iDATA (ℤ.pos 4)))))) (ULambda (UCon (tagCon pdata (bDATA (mkByteString "\ENQ"))))))

expected-chooseDataConstr : Result
expected-chooseDataConstr = success (ULambda (UCon (tagCon integer (ℤ.pos 1))))

-- Pending: bytestring inside a `data` constant.
pending-chooseDataConstr : Set
pending-chooseDataConstr = Pending (evalRaw test-chooseDataConstr ≡ expected-chooseDataConstr)
```

## chooseDataInteger

```
-- builtin/semantics/chooseDataInteger
test-chooseDataInteger : Untyped
test-chooseDataInteger = (UApp (UApp (UApp (UApp (UApp (UApp (UForce (UBuiltin chooseData)) (UCon (tagCon pdata (iDATA (ℤ.pos 5))))) (ULambda (UCon (tagCon integer (ℤ.pos 1))))) (ULambda (UCon (tagCon string "two")))) (ULambda (UVar 0))) (ULambda (UCon (tagCon pdata (iDATA (ℤ.pos 4)))))) (ULambda (UCon (tagCon pdata (bDATA (mkByteString "\ENQ"))))))

expected-chooseDataInteger : Result
expected-chooseDataInteger = success (ULambda (UCon (tagCon pdata (iDATA (ℤ.pos 4)))))

-- Pending: bytestring inside a `data` constant.
pending-chooseDataInteger : Set
pending-chooseDataInteger = Pending (evalRaw test-chooseDataInteger ≡ expected-chooseDataInteger)
```

## chooseDataList

```
-- builtin/semantics/chooseDataList
test-chooseDataList : Untyped
test-chooseDataList = (UApp (UApp (UApp (UApp (UApp (UApp (UForce (UBuiltin chooseData)) (UCon (tagCon pdata (ListDATA ((iDATA (ℤ.pos 0)) ∷ (iDATA (ℤ.pos 1)) ∷ []))))) (ULambda (UCon (tagCon integer (ℤ.pos 1))))) (ULambda (UCon (tagCon string "two")))) (ULambda (UVar 0))) (ULambda (UCon (tagCon pdata (iDATA (ℤ.pos 4)))))) (ULambda (UCon (tagCon pdata (bDATA (mkByteString "\ENQ"))))))

expected-chooseDataList : Result
expected-chooseDataList = success (ULambda (UVar 0))

-- Pending: bytestring inside a `data` constant.
pending-chooseDataList : Set
pending-chooseDataList = Pending (evalRaw test-chooseDataList ≡ expected-chooseDataList)
```

## chooseDataMap

```
-- builtin/semantics/chooseDataMap
test-chooseDataMap : Untyped
test-chooseDataMap = (UApp (UApp (UApp (UApp (UApp (UApp (UForce (UBuiltin chooseData)) (UCon (tagCon pdata (MapDATA (((iDATA (ℤ.pos 0)) , (bDATA (mkByteString "\NUL"))) ∷ ((bDATA (mkByteString "\SI")) , (iDATA (ℤ.pos 1))) ∷ []))))) (ULambda (UCon (tagCon integer (ℤ.pos 1))))) (ULambda (UCon (tagCon string "two")))) (ULambda (UVar 0))) (ULambda (UCon (tagCon pdata (iDATA (ℤ.pos 4)))))) (ULambda (UCon (tagCon pdata (bDATA (mkByteString "\ENQ"))))))

expected-chooseDataMap : Result
expected-chooseDataMap = success (ULambda (UCon (tagCon string "two")))

-- Pending: bytestring inside a `data` constant.
pending-chooseDataMap : Set
pending-chooseDataMap = Pending (evalRaw test-chooseDataMap ≡ expected-chooseDataMap)
```

## constrData

```
-- builtin/semantics/constrData
test-constrData : Untyped
test-constrData = (UApp (UApp (UBuiltin constrData) (UCon (tagCon integer (ℤ.pos 7212)))) (UCon (tagCon (list pdata) ((bDATA (mkByteString "y\211")) ∷ (ListDATA ((iDATA (ℤ.pos 44)) ∷ [])) ∷ []))))

expected-constrData : Result
expected-constrData = success (UCon (tagCon pdata (ConstrDATA (ℤ.pos 7212) ((bDATA (mkByteString "y\211")) ∷ (ListDATA ((iDATA (ℤ.pos 44)) ∷ [])) ∷ []))))

-- Pending: bytestring inside a `data` constant.
pending-constrData : Set
pending-constrData = Pending (evalRaw test-constrData ≡ expected-constrData)
```

## encodeUtf8

```
-- builtin/semantics/encodeUtf8
test-encodeUtf8 : Untyped
test-encodeUtf8 = (UApp (UBuiltin encodeUtf8) (UCon (tagCon string "Ola")))

expected-encodeUtf8 : Result
expected-encodeUtf8 = success (UCon (tagCon bytestring (mkByteString "Ola")))

-- Pending: bytestring constant; postulated builtin `encodeUtf8`.
pending-encodeUtf8 : Set
pending-encodeUtf8 = Pending (evalRaw test-encodeUtf8 ≡ expected-encodeUtf8)
```

## fstPair

```
-- builtin/semantics/fstPair
test-fstPair : Untyped
test-fstPair = (UApp (UForce (UForce (UBuiltin fstPair))) (UCon (tagCon (pair bool bytestring) (true , (mkByteString "\SOH#E")))))

expected-fstPair : Result
expected-fstPair = success (UCon (tagCon bool true))

-- Pending: bytestring constant.
pending-fstPair : Set
pending-fstPair = Pending (evalRaw test-fstPair ≡ expected-fstPair)
```

## iData

```
-- builtin/semantics/iData
test-iData : Untyped
test-iData = (UApp (UBuiltin iData) (UCon (tagCon integer (ℤ.pos 0))))

expected-iData : Result
expected-iData = success (UCon (tagCon pdata (iDATA (ℤ.pos 0))))

_ : evalRaw test-iData ≡ expected-iData
_ = refl
```

## lengthOfByteString

```
-- builtin/semantics/lengthOfByteString
test-lengthOfByteString : Untyped
test-lengthOfByteString = (UApp (UBuiltin lengthOfByteString) (UCon (tagCon bytestring (mkByteString "\NUL\255\170"))))

expected-lengthOfByteString : Result
expected-lengthOfByteString = success (UCon (tagCon integer (ℤ.pos 3)))

-- Pending: bytestring constant; postulated builtin `lengthOfByteString`.
pending-lengthOfByteString : Set
pending-lengthOfByteString = Pending (evalRaw test-lengthOfByteString ≡ expected-lengthOfByteString)
```

## listData

```
-- builtin/semantics/listData
test-listData : Untyped
test-listData = (UApp (UBuiltin listData) (UCon (tagCon (list pdata) ((iDATA (ℤ.pos 0)) ∷ (bDATA (mkByteString "\DC24")) ∷ (MapDATA (((iDATA (ℤ.pos 9)) , (ListDATA ((bDATA (mkByteString "\171\205")) ∷ []))) ∷ ((bDATA (mkByteString "C!")) , (iDATA (ℤ.pos 1234))) ∷ [])) ∷ []))))

expected-listData : Result
expected-listData = success (UCon (tagCon pdata (ListDATA ((iDATA (ℤ.pos 0)) ∷ (bDATA (mkByteString "\DC24")) ∷ (MapDATA (((iDATA (ℤ.pos 9)) , (ListDATA ((bDATA (mkByteString "\171\205")) ∷ []))) ∷ ((bDATA (mkByteString "C!")) , (iDATA (ℤ.pos 1234))) ∷ [])) ∷ []))))

-- Pending: bytestring inside a `data` constant.
pending-listData : Set
pending-listData = Pending (evalRaw test-listData ≡ expected-listData)
```

## listOfList

```
-- builtin/semantics/listOfList
test-listOfList : Untyped
test-listOfList = (UCon (tagCon (list (list integer)) (((ℤ.pos 0) ∷ []) ∷ ((ℤ.pos 0) ∷ (ℤ.pos 1) ∷ (ℤ.pos 2) ∷ []) ∷ ((ℤ.pos 4) ∷ (ℤ.pos 5) ∷ (ℤ.pos 2) ∷ []) ∷ [])))

expected-listOfList : Result
expected-listOfList = success (UCon (tagCon (list (list integer)) (((ℤ.pos 0) ∷ []) ∷ ((ℤ.pos 0) ∷ (ℤ.pos 1) ∷ (ℤ.pos 2) ∷ []) ∷ ((ℤ.pos 4) ∷ (ℤ.pos 5) ∷ (ℤ.pos 2) ∷ []) ∷ [])))

_ : evalRaw test-listOfList ≡ expected-listOfList
_ = refl
```

## listOfPair

```
-- builtin/semantics/listOfPair
test-listOfPair : Untyped
test-listOfPair = (UCon (tagCon (list (pair integer bool)) (((ℤ.pos 1) , true) ∷ ((ℤ.pos 500000) , false) ∷ ((ℤ.pos 0) , true) ∷ [])))

expected-listOfPair : Result
expected-listOfPair = success (UCon (tagCon (list (pair integer bool)) (((ℤ.pos 1) , true) ∷ ((ℤ.pos 500000) , false) ∷ ((ℤ.pos 0) , true) ∷ [])))

_ : evalRaw test-listOfPair ≡ expected-listOfPair
_ = refl
```

## mapData

```
-- builtin/semantics/mapData
test-mapData : Untyped
test-mapData = (UApp (UBuiltin mapData) (UCon (tagCon (list (pair pdata pdata)) (((iDATA (ℤ.pos 99)) , (bDATA (mkByteString "\DC24"))) ∷ ((ListDATA ((ListDATA ((bDATA (mkByteString "\239\SOH")) ∷ (iDATA (ℤ.negsuc 84)) ∷ [])) ∷ [])) , (MapDATA ([]))) ∷ []))))

expected-mapData : Result
expected-mapData = success (UCon (tagCon pdata (MapDATA (((iDATA (ℤ.pos 99)) , (bDATA (mkByteString "\DC24"))) ∷ ((ListDATA ((ListDATA ((bDATA (mkByteString "\239\SOH")) ∷ (iDATA (ℤ.negsuc 84)) ∷ [])) ∷ [])) , (MapDATA ([]))) ∷ []))))

-- Pending: bytestring inside a `data` constant.
pending-mapData : Set
pending-mapData = Pending (evalRaw test-mapData ≡ expected-mapData)
```

## mkNilData

```
-- builtin/semantics/mkNilData
test-mkNilData : Untyped
test-mkNilData = (UApp (UBuiltin mkNilData) (UCon (tagCon unit tt)))

expected-mkNilData : Result
expected-mkNilData = success (UCon (tagCon (list pdata) ([])))

_ : evalRaw test-mkNilData ≡ expected-mkNilData
_ = refl
```

## mkNilPairData

```
-- builtin/semantics/mkNilPairData
test-mkNilPairData : Untyped
test-mkNilPairData = (UApp (UBuiltin mkNilPairData) (UCon (tagCon unit tt)))

expected-mkNilPairData : Result
expected-mkNilPairData = success (UCon (tagCon (list (pair pdata pdata)) ([])))

_ : evalRaw test-mkNilPairData ≡ expected-mkNilPairData
_ = refl
```

## mkPairData

```
-- builtin/semantics/mkPairData
test-mkPairData : Untyped
test-mkPairData = (UApp (UApp (UBuiltin mkPairData) (UCon (tagCon pdata (ListDATA ((iDATA (ℤ.pos 0)) ∷ (bDATA (mkByteString "\255")) ∷ []))))) (UCon (tagCon pdata (ConstrDATA (ℤ.pos 1234) ((iDATA (ℤ.pos 3)) ∷ [])))))

expected-mkPairData : Result
expected-mkPairData = success (UCon (tagCon (pair pdata pdata) ((ListDATA ((iDATA (ℤ.pos 0)) ∷ (bDATA (mkByteString "\255")) ∷ [])) , (ConstrDATA (ℤ.pos 1234) ((iDATA (ℤ.pos 3)) ∷ [])))))

-- Pending: bytestring inside a `data` constant.
pending-mkPairData : Set
pending-mkPairData = Pending (evalRaw test-mkPairData ≡ expected-mkPairData)
```

## pairOfPairAndList

```
-- builtin/semantics/pairOfPairAndList
test-pairOfPairAndList : Untyped
test-pairOfPairAndList = (UCon (tagCon (pair (pair bool bytestring) (list integer)) ((true , (mkByteString "\SOH#E")) , ((ℤ.pos 0) ∷ (ℤ.pos 1) ∷ (ℤ.pos 2) ∷ []))))

expected-pairOfPairAndList : Result
expected-pairOfPairAndList = success (UCon (tagCon (pair (pair bool bytestring) (list integer)) ((true , (mkByteString "\SOH#E")) , ((ℤ.pos 0) ∷ (ℤ.pos 1) ∷ (ℤ.pos 2) ∷ []))))

-- Pending: bytestring constant.
pending-pairOfPairAndList : Set
pending-pairOfPairAndList = Pending (evalRaw test-pairOfPairAndList ≡ expected-pairOfPairAndList)
```

## sndPair

```
-- builtin/semantics/sndPair
test-sndPair : Untyped
test-sndPair = (UApp (UForce (UForce (UBuiltin sndPair))) (UCon (tagCon (pair bool bytestring) (true , (mkByteString "\SOH#E")))))

expected-sndPair : Result
expected-sndPair = success (UCon (tagCon bytestring (mkByteString "\SOH#E")))

-- Pending: bytestring constant.
pending-sndPair : Set
pending-sndPair = Pending (evalRaw test-sndPair ≡ expected-sndPair)
```

## subtractInteger-non-iter

```
-- builtin/semantics/subtractInteger-non-iter
test-subtractInteger-non-iter : Untyped
test-subtractInteger-non-iter = (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 2))))

expected-subtractInteger-non-iter : Result
expected-subtractInteger-non-iter = success (UCon (tagCon integer (ℤ.negsuc 0)))

_ : evalRaw test-subtractInteger-non-iter ≡ expected-subtractInteger-non-iter
_ = refl
```

## trace

```
-- builtin/semantics/trace
test-trace : Untyped
test-trace = (UApp (UApp (UForce (UBuiltin trace)) (UCon (tagCon string "Ola"))) (UCon (tagCon integer (ℤ.pos 2))))

expected-trace : Result
expected-trace = success (UCon (tagCon integer (ℤ.pos 2)))

_ : evalRaw test-trace ≡ expected-trace
_ = refl
```
