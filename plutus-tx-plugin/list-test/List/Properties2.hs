{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
-- CSE is very unstable and produces different output, likely depending on the version of either
-- @unordered-containers@ or @hashable@.
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}

{-# HLINT ignore "Use elemIndex" #-}

module List.Properties2 where

import Hedgehog (Property, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusTx.Code
import PlutusTx.Data.List qualified as Data
import PlutusTx.Data.List qualified as Data.List
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.List qualified as List
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.TH (compile)
import PlutusTx.Test.Run.Code (evaluationResultMatchesHaskell)

import List.Semantics

listToMaybeProgram :: CompiledCode ([Integer] -> Maybe Integer)
listToMaybeProgram = $$(compile [||List.listToMaybe||])

dataListToMaybeProgram :: CompiledCode (Data.List Integer -> Maybe Integer)
dataListToMaybeProgram = $$(compile [||Data.List.listToMaybe||])

listToMaybeSpec :: Property
listToMaybeSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = listToMaybeS listS
  evaluationResultMatchesHaskell
    (listToMaybeProgram `unsafeApplyCode` liftCodeDef list)
    (===)
    expected
  evaluationResultMatchesHaskell
    (dataListToMaybeProgram `unsafeApplyCode` liftCodeDef dataList)
    (===)
    expected

uniqueElementProgram :: CompiledCode ([Integer] -> Maybe Integer)
uniqueElementProgram = $$(compile [||List.uniqueElement||])

dataUniqueElementProgram :: CompiledCode (Data.List Integer -> Maybe Integer)
dataUniqueElementProgram = $$(compile [||Data.List.uniqueElement||])

uniqueElementSpec :: Property
uniqueElementSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = uniqueElementS listS
  evaluationResultMatchesHaskell
    (uniqueElementProgram `unsafeApplyCode` liftCodeDef list)
    (===)
    expected
  evaluationResultMatchesHaskell
    (dataUniqueElementProgram `unsafeApplyCode` liftCodeDef dataList)
    (===)
    expected

indexProgram :: CompiledCode ([Integer] -> Integer -> Integer)
indexProgram = $$(compile [||\l i -> l List.!! i||])

dataIndexProgram :: CompiledCode (Data.List Integer -> Integer -> Integer)
dataIndexProgram = $$(compile [||\l i -> l Data.List.!! i||])

indexSpec :: Property
indexSpec = property $ do
  listS <- forAll genNonEmptyListS
  num <- forAll $ Gen.integral (Range.linear 0 (lengthS listS - 1))
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = indexS listS num
  evaluationResultMatchesHaskell
    ( indexProgram
        `unsafeApplyCode` liftCodeDef list
        `unsafeApplyCode` liftCodeDef num
    )
    (===)
    expected
  evaluationResultMatchesHaskell
    ( dataIndexProgram
        `unsafeApplyCode` liftCodeDef dataList
        `unsafeApplyCode` liftCodeDef num
    )
    (===)
    expected

revAppendProgram :: CompiledCode ([Integer] -> [Integer] -> [Integer])
revAppendProgram = $$(compile [||List.revAppend||])

dataRevAppendProgram :: CompiledCode (Data.List Integer -> Data.List Integer -> Data.List Integer)
dataRevAppendProgram = $$(compile [||Data.List.revAppend||])

revAppendSpec :: Property
revAppendSpec = property $ do
  listS1 <- forAll genListS
  listS2 <- forAll genListS
  let list1 = semanticsToList listS1
      list2 = semanticsToList listS2
      dataList1 = semanticsToDataList listS1
      dataList2 = semanticsToDataList listS2
      expected = revAppendS listS1 listS2
  evaluationResultMatchesHaskell
    ( revAppendProgram
        `unsafeApplyCode` liftCodeDef list1
        `unsafeApplyCode` liftCodeDef list2
    )
    (===)
    (semanticsToList expected)
  evaluationResultMatchesHaskell
    ( dataRevAppendProgram
        `unsafeApplyCode` liftCodeDef dataList1
        `unsafeApplyCode` liftCodeDef dataList2
    )
    (===)
    (semanticsToDataList expected)

reverseProgram :: CompiledCode ([Integer] -> [Integer])
reverseProgram = $$(compile [||List.reverse||])

dataReverseProgram :: CompiledCode (Data.List Integer -> Data.List Integer)
dataReverseProgram = $$(compile [||Data.List.reverse||])

reverseSpec :: Property
reverseSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = reverseS listS
  evaluationResultMatchesHaskell
    (reverseProgram `unsafeApplyCode` liftCodeDef list)
    (===)
    (semanticsToList expected)
  evaluationResultMatchesHaskell
    (dataReverseProgram `unsafeApplyCode` liftCodeDef dataList)
    (===)
    (semanticsToDataList expected)

findIndexProgram :: CompiledCode (Integer -> [Integer] -> Maybe Integer)
findIndexProgram = $$(compile [||\num -> List.findIndex (PlutusTx.== num)||])

dataFindIndexProgram :: CompiledCode (Integer -> Data.List Integer -> Maybe Integer)
dataFindIndexProgram = $$(compile [||\num -> Data.List.findIndex (PlutusTx.== num)||])

findIndexSpec :: Property
findIndexSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = findIndexS (== num) listS
  evaluationResultMatchesHaskell
    ( findIndexProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  evaluationResultMatchesHaskell
    ( dataFindIndexProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

unzipProgram :: CompiledCode ([(Integer, Integer)] -> ([Integer], [Integer]))
unzipProgram = $$(compile [||List.unzip||])

dataUnzipProgram
  :: CompiledCode
       (Data.List (Integer, Integer) -> (Data.List Integer, Data.List Integer))
dataUnzipProgram = $$(compile [||Data.List.unzip||])

unzipSpec :: Property
unzipSpec = property $ do
  listS <- forAll genListSPair
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      (expected1, expected2) = unzipS listS
  evaluationResultMatchesHaskell
    (unzipProgram `unsafeApplyCode` liftCodeDef list)
    (===)
    (semanticsToList expected1, semanticsToList expected2)
  evaluationResultMatchesHaskell
    (dataUnzipProgram `unsafeApplyCode` liftCodeDef dataList)
    (===)
    (semanticsToDataList expected1, semanticsToDataList expected2)

zipWithProgram :: CompiledCode ([Integer] -> [Integer] -> [Integer])
zipWithProgram = $$(compile [||List.zipWith (PlutusTx.-)||])

dataZipWithProgram :: CompiledCode (Data.List Integer -> Data.List Integer -> Data.List Integer)
dataZipWithProgram = $$(compile [||Data.List.zipWith (PlutusTx.-)||])

zipWithSpec :: Property
zipWithSpec = property $ do
  listS1 <- forAll genListS
  listS2 <- forAll genListS
  let list1 = semanticsToList listS1
      list2 = semanticsToList listS2
      dataList1 = semanticsToDataList listS1
      dataList2 = semanticsToDataList listS2
      expected = zipWithS (-) listS1 listS2
  evaluationResultMatchesHaskell
    ( zipWithProgram
        `unsafeApplyCode` liftCodeDef list1
        `unsafeApplyCode` liftCodeDef list2
    )
    (===)
    (semanticsToList expected)
  evaluationResultMatchesHaskell
    ( dataZipWithProgram
        `unsafeApplyCode` liftCodeDef dataList1
        `unsafeApplyCode` liftCodeDef dataList2
    )
    (===)
    (semanticsToDataList expected)

headProgram :: CompiledCode ([Integer] -> Integer)
headProgram = $$(compile [||List.head||])

dataHeadProgram :: CompiledCode (Data.List Integer -> Integer)
dataHeadProgram = $$(compile [||Data.List.head||])

headSpec :: Property
headSpec = property $ do
  listS <- forAll genNonEmptyListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = headS listS
  evaluationResultMatchesHaskell
    (headProgram `unsafeApplyCode` liftCodeDef list)
    (===)
    expected
  evaluationResultMatchesHaskell
    (dataHeadProgram `unsafeApplyCode` liftCodeDef dataList)
    (===)
    expected

lastProgram :: CompiledCode ([Integer] -> Integer)
lastProgram = $$(compile [||List.last||])

dataLastProgram :: CompiledCode (Data.List Integer -> Integer)
dataLastProgram = $$(compile [||Data.List.last||])

lastSpec :: Property
lastSpec = property $ do
  listS <- forAll genNonEmptyListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = lastS listS
  evaluationResultMatchesHaskell
    (lastProgram `unsafeApplyCode` liftCodeDef list)
    (===)
    expected
  evaluationResultMatchesHaskell
    (dataLastProgram `unsafeApplyCode` liftCodeDef dataList)
    (===)
    expected

tailProgram :: CompiledCode ([Integer] -> [Integer])
tailProgram = $$(compile [||List.tail||])

dataTailProgram :: CompiledCode (Data.List Integer -> Data.List Integer)
dataTailProgram = $$(compile [||Data.List.tail||])

tailSpec :: Property
tailSpec = property $ do
  listS <- forAll genNonEmptyListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = tailS listS
  evaluationResultMatchesHaskell
    (tailProgram `unsafeApplyCode` liftCodeDef list)
    (===)
    (semanticsToList expected)
  evaluationResultMatchesHaskell
    (dataTailProgram `unsafeApplyCode` liftCodeDef dataList)
    (===)
    (semanticsToDataList expected)

takeProgram :: CompiledCode (Integer -> [Integer] -> [Integer])
takeProgram = $$(compile [||List.take||])

dataTakeProgram :: CompiledCode (Integer -> Data.List Integer -> Data.List Integer)
dataTakeProgram = $$(compile [||Data.List.take||])

takeSpec :: Property
takeSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = takeS num listS
  evaluationResultMatchesHaskell
    ( takeProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  evaluationResultMatchesHaskell
    ( dataTakeProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

dropProgram :: CompiledCode (Integer -> [Integer] -> [Integer])
dropProgram = $$(compile [||List.drop||])

dataDropProgram :: CompiledCode (Integer -> Data.List Integer -> Data.List Integer)
dataDropProgram = $$(compile [||Data.List.drop||])

dropSpec :: Property
dropSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = dropS num listS
  evaluationResultMatchesHaskell
    ( dropProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  evaluationResultMatchesHaskell
    ( dataDropProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

dropWhileProgram :: CompiledCode ([Integer] -> [Integer])
dropWhileProgram = $$(compile [||List.dropWhile PlutusTx.even||])

dataDropWhileProgram :: CompiledCode (Data.List Integer -> Data.List Integer)
dataDropWhileProgram = $$(compile [||Data.List.dropWhile PlutusTx.even||])

dropWhileSpec :: Property
dropWhileSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = dropWhileS even listS
  evaluationResultMatchesHaskell
    (dropWhileProgram `unsafeApplyCode` liftCodeDef list)
    (===)
    (semanticsToList expected)
  evaluationResultMatchesHaskell
    (dataDropWhileProgram `unsafeApplyCode` liftCodeDef dataList)
    (===)
    (semanticsToDataList expected)

splitAtProgram :: CompiledCode (Integer -> [Integer] -> ([Integer], [Integer]))
splitAtProgram = $$(compile [||List.splitAt||])

dataSplitAtProgram
  :: CompiledCode (Integer -> Data.List Integer -> (Data.List Integer, Data.List Integer))
dataSplitAtProgram = $$(compile [||Data.List.splitAt||])

splitAtSpec :: Property
splitAtSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      (expected1, expected2) = splitAtS num listS
  evaluationResultMatchesHaskell
    ( splitAtProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected1, semanticsToList expected2)
  evaluationResultMatchesHaskell
    ( dataSplitAtProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected1, semanticsToDataList expected2)

elemByProgram :: CompiledCode (Integer -> [Integer] -> Bool)
elemByProgram = $$(compile [||\n -> List.elemBy (PlutusTx.<) n||])

dataElemByProgram :: CompiledCode (Integer -> Data.List Integer -> Bool)
dataElemByProgram = $$(compile [||\n -> Data.List.elemBy (PlutusTx.<) n||])

elemBySpec :: Property
elemBySpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = elemByS (<) num listS
  evaluationResultMatchesHaskell
    ( elemByProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  evaluationResultMatchesHaskell
    ( dataElemByProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

nubByProgram :: CompiledCode ([Integer] -> [Integer])
nubByProgram = $$(compile [||List.nubBy (PlutusTx.>=)||])

dataNubByProgram :: CompiledCode (Data.List Integer -> Data.List Integer)
dataNubByProgram = $$(compile [||Data.List.nubBy (PlutusTx.>=)||])

nubBySpec :: Property
nubBySpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = nubByS (>=) listS
  evaluationResultMatchesHaskell
    (nubByProgram `unsafeApplyCode` liftCodeDef list)
    (===)
    (semanticsToList expected)
  evaluationResultMatchesHaskell
    (dataNubByProgram `unsafeApplyCode` liftCodeDef dataList)
    (===)
    (semanticsToDataList expected)

nubProgram :: CompiledCode ([Integer] -> [Integer])
nubProgram = $$(compile [||List.nub||])

dataNubProgram :: CompiledCode (Data.List Integer -> Data.List Integer)
dataNubProgram = $$(compile [||Data.List.nub||])

nubSpec :: Property
nubSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = nubS listS
  evaluationResultMatchesHaskell
    (nubProgram `unsafeApplyCode` liftCodeDef list)
    (===)
    (semanticsToList expected)
  evaluationResultMatchesHaskell
    (dataNubProgram `unsafeApplyCode` liftCodeDef dataList)
    (===)
    (semanticsToDataList expected)

partitionProgram :: CompiledCode ([Integer] -> ([Integer], [Integer]))
partitionProgram = $$(compile [||List.partition PlutusTx.even||])

dataPartitionProgram :: CompiledCode (Data.List Integer -> (Data.List Integer, Data.List Integer))
dataPartitionProgram = $$(compile [||Data.List.partition PlutusTx.even||])

partitionSpec :: Property
partitionSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      (expected1, expected2) = partitionS even listS
  evaluationResultMatchesHaskell
    ( partitionProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected1, semanticsToList expected2)
  evaluationResultMatchesHaskell
    (dataPartitionProgram `unsafeApplyCode` liftCodeDef dataList)
    (===)
    (semanticsToDataList expected1, semanticsToDataList expected2)

replicateProgram :: CompiledCode (Integer -> Integer -> [Integer])
replicateProgram = $$(compile [||List.replicate||])

dataReplicateProgram :: CompiledCode (Integer -> Integer -> Data.List Integer)
dataReplicateProgram = $$(compile [||Data.List.replicate||])

replicateSpec :: Property
replicateSpec = property $ do
  num1 <- forAll $ Gen.integral rangeElem
  num2 <- forAll $ Gen.integral rangeElem
  let expected = replicateS num1 num2
  evaluationResultMatchesHaskell
    ( replicateProgram
        `unsafeApplyCode` liftCodeDef num1
        `unsafeApplyCode` liftCodeDef num2
    )
    (===)
    (semanticsToList expected)
  evaluationResultMatchesHaskell
    ( dataReplicateProgram
        `unsafeApplyCode` liftCodeDef num1
        `unsafeApplyCode` liftCodeDef num2
    )
    (===)
    (semanticsToDataList expected)
