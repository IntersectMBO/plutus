
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
-- CSE is very unstable and produces different output, likely depending on the version of either
-- @unordered-containers@ or @hashable@.
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use elemIndex" #-}

module List.Properties2 where

import PlutusTx.Code
import PlutusTx.Data.List qualified as Data
import PlutusTx.Data.List qualified as Data.List
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.List qualified as List
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test.Util.Compiled (cekResultMatchesHaskellValue, compiledCodeToTerm)
import PlutusTx.TH (compile)

import Hedgehog (Property, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import List.Semantics

listToMaybeProgram :: CompiledCode ([Integer] -> Maybe Integer)
listToMaybeProgram = $$(compile [|| List.listToMaybe ||])

dataListToMaybeProgram :: CompiledCode (Data.List Integer -> Maybe Integer)
dataListToMaybeProgram = $$(compile [|| Data.List.listToMaybe ||])

listToMaybeSpec :: Property
listToMaybeSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = listToMaybeS listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ listToMaybeProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataListToMaybeProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

uniqueElementProgram :: CompiledCode ([Integer] -> Maybe Integer)
uniqueElementProgram = $$(compile [|| List.uniqueElement ||])

dataUniqueElementProgram :: CompiledCode (Data.List Integer -> Maybe Integer)
dataUniqueElementProgram = $$(compile [|| Data.List.uniqueElement ||])

uniqueElementSpec :: Property
uniqueElementSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = uniqueElementS listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ uniqueElementProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataUniqueElementProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected


indexProgram :: CompiledCode ([Integer] -> Integer -> Integer)
indexProgram = $$(compile [|| \l i -> l List.!! i ||])

dataIndexProgram :: CompiledCode (Data.List Integer -> Integer -> Integer)
dataIndexProgram = $$(compile [|| \l i -> l Data.List.!! i ||])

indexSpec :: Property
indexSpec = property $ do
  listS <- forAll genNonEmptyListS
  num <- forAll $ Gen.integral (Range.linear 0 (lengthS listS - 1))
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = indexS listS num
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ indexProgram
        `unsafeApplyCode` liftCodeDef list
        `unsafeApplyCode` liftCodeDef num
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataIndexProgram
        `unsafeApplyCode` liftCodeDef dataList
        `unsafeApplyCode` liftCodeDef num
    )
    (===)
    expected

revAppendProgram :: CompiledCode ([Integer] -> [Integer] -> [Integer])
revAppendProgram = $$(compile [|| List.revAppend ||])

dataRevAppendProgram :: CompiledCode (Data.List Integer -> Data.List Integer -> Data.List Integer)
dataRevAppendProgram = $$(compile [|| Data.List.revAppend ||])

revAppendSpec :: Property
revAppendSpec = property $ do
  listS1 <- forAll genListS
  listS2 <- forAll genListS
  let list1 = semanticsToList listS1
      list2 = semanticsToList listS2
      dataList1 = semanticsToDataList listS1
      dataList2 = semanticsToDataList listS2
      expected = revAppendS listS1 listS2
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ revAppendProgram
        `unsafeApplyCode` liftCodeDef list1
        `unsafeApplyCode` liftCodeDef list2
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataRevAppendProgram
        `unsafeApplyCode` liftCodeDef dataList1
        `unsafeApplyCode` liftCodeDef dataList2
    )
    (===)
    (semanticsToDataList expected)

reverseProgram :: CompiledCode ([Integer] -> [Integer])
reverseProgram = $$(compile [|| List.reverse ||])

dataReverseProgram :: CompiledCode (Data.List Integer -> Data.List Integer)
dataReverseProgram = $$(compile [|| Data.List.reverse ||])

reverseSpec :: Property
reverseSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = reverseS listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ reverseProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataReverseProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

findIndexProgram :: CompiledCode (Integer -> [Integer] -> Maybe Integer)
findIndexProgram = $$(compile [|| \num -> List.findIndex (PlutusTx.== num) ||])

dataFindIndexProgram :: CompiledCode (Integer -> Data.List Integer -> Maybe Integer)
dataFindIndexProgram = $$(compile [|| \num -> Data.List.findIndex (PlutusTx.== num) ||])

findIndexSpec :: Property
findIndexSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = findIndexS (== num) listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ findIndexProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataFindIndexProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

unzipProgram :: CompiledCode ([(Integer, Integer)] -> ([Integer], [Integer]))
unzipProgram = $$(compile [|| List.unzip ||])

dataUnzipProgram
  :: CompiledCode
      (Data.List (Integer, Integer) -> (Data.List Integer, Data.List Integer))
dataUnzipProgram = $$(compile [|| Data.List.unzip ||])

unzipSpec :: Property
unzipSpec = property $ do
  listS <- forAll genListSPair
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      (expected1, expected2) = unzipS listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ unzipProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected1, semanticsToList expected2)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataUnzipProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected1, semanticsToDataList expected2)

zipWithProgram :: CompiledCode ([Integer] -> [Integer] -> [Integer])
zipWithProgram = $$(compile [|| List.zipWith (PlutusTx.-) ||])

dataZipWithProgram :: CompiledCode (Data.List Integer -> Data.List Integer -> Data.List Integer)
dataZipWithProgram = $$(compile [|| Data.List.zipWith (PlutusTx.-) ||])

zipWithSpec :: Property
zipWithSpec = property $ do
  listS1 <- forAll genListS
  listS2 <- forAll genListS
  let list1 = semanticsToList listS1
      list2 = semanticsToList listS2
      dataList1 = semanticsToDataList listS1
      dataList2 = semanticsToDataList listS2
      expected = zipWithS (-) listS1 listS2
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ zipWithProgram
        `unsafeApplyCode` liftCodeDef list1
        `unsafeApplyCode` liftCodeDef list2
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataZipWithProgram
        `unsafeApplyCode` liftCodeDef dataList1
        `unsafeApplyCode` liftCodeDef dataList2
    )
    (===)
    (semanticsToDataList expected)

headProgram :: CompiledCode ([Integer] -> Integer)
headProgram = $$(compile [|| List.head ||])

dataHeadProgram :: CompiledCode (Data.List Integer -> Integer)
dataHeadProgram = $$(compile [|| Data.List.head ||])

headSpec :: Property
headSpec = property $ do
  listS <- forAll genNonEmptyListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = headS listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ headProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataHeadProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

lastProgram :: CompiledCode ([Integer] -> Integer)
lastProgram = $$(compile [|| List.last ||])

dataLastProgram :: CompiledCode (Data.List Integer -> Integer)
dataLastProgram = $$(compile [|| Data.List.last ||])

lastSpec :: Property
lastSpec = property $ do
  listS <- forAll genNonEmptyListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = lastS listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ lastProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataLastProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

tailProgram :: CompiledCode ([Integer] -> [Integer])
tailProgram = $$(compile [|| List.tail ||])

dataTailProgram :: CompiledCode (Data.List Integer -> Data.List Integer)
dataTailProgram = $$(compile [|| Data.List.tail ||])

tailSpec :: Property
tailSpec = property $ do
  listS <- forAll genNonEmptyListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = tailS listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ tailProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataTailProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

takeProgram :: CompiledCode (Integer -> [Integer] -> [Integer])
takeProgram = $$(compile [|| List.take ||])

dataTakeProgram :: CompiledCode (Integer -> Data.List Integer -> Data.List Integer)
dataTakeProgram = $$(compile [|| Data.List.take ||])

takeSpec :: Property
takeSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = takeS num listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ takeProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataTakeProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

dropProgram :: CompiledCode (Integer -> [Integer] -> [Integer])
dropProgram = $$(compile [|| List.drop ||])

dataDropProgram :: CompiledCode (Integer -> Data.List Integer -> Data.List Integer)
dataDropProgram = $$(compile [|| Data.List.drop ||])

dropSpec :: Property
dropSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = dropS num listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dropProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataDropProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

dropWhileProgram :: CompiledCode ([Integer] -> [Integer])
dropWhileProgram = $$(compile [|| List.dropWhile PlutusTx.even ||])

dataDropWhileProgram :: CompiledCode (Data.List Integer -> Data.List Integer)
dataDropWhileProgram = $$(compile [|| Data.List.dropWhile PlutusTx.even ||])

dropWhileSpec :: Property
dropWhileSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = dropWhileS even listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dropWhileProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataDropWhileProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

splitAtProgram :: CompiledCode (Integer -> [Integer] -> ([Integer], [Integer]))
splitAtProgram = $$(compile [|| List.splitAt ||])

dataSplitAtProgram
  :: CompiledCode
      (Integer -> Data.List Integer -> (Data.List Integer, Data.List Integer))
dataSplitAtProgram = $$(compile [|| Data.List.splitAt ||])

splitAtSpec :: Property
splitAtSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      (expected1, expected2) = splitAtS num listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ splitAtProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected1, semanticsToList expected2)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataSplitAtProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected1, semanticsToDataList expected2)

elemByProgram :: CompiledCode (Integer -> [Integer] -> Bool)
elemByProgram = $$(compile [|| \n -> List.elemBy (PlutusTx.<) n ||])

dataElemByProgram :: CompiledCode (Integer -> Data.List Integer -> Bool)
dataElemByProgram = $$(compile [|| \n -> Data.List.elemBy (PlutusTx.<) n ||])

elemBySpec :: Property
elemBySpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = elemByS (<) num listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ elemByProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataElemByProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

nubByProgram :: CompiledCode ([Integer] -> [Integer])
nubByProgram = $$(compile [|| List.nubBy (PlutusTx.>=) ||])

dataNubByProgram :: CompiledCode (Data.List Integer -> Data.List Integer)
dataNubByProgram = $$(compile [|| Data.List.nubBy (PlutusTx.>=) ||])

nubBySpec :: Property
nubBySpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = nubByS (>=) listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ nubByProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataNubByProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

nubProgram :: CompiledCode ([Integer] -> [Integer])
nubProgram = $$(compile [|| List.nub ||])

dataNubProgram :: CompiledCode (Data.List Integer -> Data.List Integer)
dataNubProgram = $$(compile [|| Data.List.nub ||])

nubSpec :: Property
nubSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = nubS listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ nubProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataNubProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

partitionProgram :: CompiledCode ([Integer] -> ([Integer], [Integer]))
partitionProgram = $$(compile [|| List.partition PlutusTx.even ||])

dataPartitionProgram :: CompiledCode (Data.List Integer -> (Data.List Integer, Data.List Integer))
dataPartitionProgram = $$(compile [|| Data.List.partition PlutusTx.even ||])

partitionSpec :: Property
partitionSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      (expected1, expected2) = partitionS even listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ partitionProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected1, semanticsToList expected2)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataPartitionProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected1, semanticsToDataList expected2)

replicateProgram :: CompiledCode (Integer -> Integer -> [Integer])
replicateProgram = $$(compile [|| List.replicate ||])

dataReplicateProgram :: CompiledCode (Integer -> Integer -> Data.List Integer)
dataReplicateProgram = $$(compile [|| Data.List.replicate ||])

replicateSpec :: Property
replicateSpec = property $ do
  num1 <- forAll $ Gen.integral rangeElem
  num2 <- forAll $ Gen.integral rangeElem
  let expected = replicateS num1 num2
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ replicateProgram
        `unsafeApplyCode` liftCodeDef num1
        `unsafeApplyCode` liftCodeDef num2
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataReplicateProgram
        `unsafeApplyCode` liftCodeDef num1
        `unsafeApplyCode` liftCodeDef num2
    )
    (===)
    (semanticsToDataList expected)
