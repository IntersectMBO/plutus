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

module List.Properties1 where

import PlutusTx.Builtins as B
import PlutusTx.Code
import PlutusTx.Data.List qualified as Data
import PlutusTx.Data.List qualified as Data.List
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.List qualified as List
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test.Util.Compiled (cekResultMatchesHaskellValue, compiledCodeToTerm)
import PlutusTx.TH (compile)

import Data.List qualified as Haskell

import Hedgehog (Property, forAll, property, (===))
import Hedgehog.Gen qualified as Gen

import List.Semantics

toSOPProgram :: CompiledCode (Data.List Integer -> [Integer])
toSOPProgram = $$(compile [|| Data.List.toSOP ||])

fromSOPProgram :: CompiledCode ([Integer] -> Data.List Integer)
fromSOPProgram = $$(compile [|| Data.List.fromSOP ||])

toSOPSpec :: Property
toSOPSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToDataList listS
      expected = semanticsToList listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ toSOPProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected

fromSOPSpec :: Property
fromSOPSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      expected = semanticsToDataList listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ fromSOPProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected

appendProgram :: CompiledCode ([Integer] -> [Integer] -> [Integer])
appendProgram = $$(compile [|| (List.++) ||])

dataAppendProgram :: CompiledCode (Data.List Integer -> Data.List Integer -> Data.List Integer)
dataAppendProgram = $$(compile [|| Data.List.append ||])

appendSpec :: Property
appendSpec = property $ do
  listS1 <- forAll genListS
  listS2 <- forAll genListS
  let list1 = semanticsToList listS1
      list2 = semanticsToList listS2
      dataList1 = semanticsToDataList listS1
      dataList2 = semanticsToDataList listS2
      expected = appendS listS1 listS2
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ appendProgram
        `unsafeApplyCode` liftCodeDef list1
        `unsafeApplyCode` liftCodeDef list2
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataAppendProgram
        `unsafeApplyCode` liftCodeDef dataList1
        `unsafeApplyCode` liftCodeDef dataList2
    )
    (===)
    (semanticsToDataList expected)

findProgram :: CompiledCode (Integer -> [Integer] -> Maybe Integer)
findProgram = $$(compile [|| \n -> List.find (\x -> x PlutusTx.> n) ||])

dataFindProgram :: CompiledCode (Integer -> Data.List Integer -> Maybe Integer)
dataFindProgram = $$(compile [|| \n -> Data.List.find (\x -> x PlutusTx.> n) ||])

findSpec :: Property
findSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = findS (> num) listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ findProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataFindProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

findIndicesProgram :: CompiledCode (Integer -> [Integer] -> [Integer])
findIndicesProgram = $$(compile [|| \n -> List.findIndices (\x -> x PlutusTx.> n) ||])

dataFindIndicesProgram :: CompiledCode (Integer -> Data.List Integer -> Data.List Integer)
dataFindIndicesProgram = $$(compile [|| \n -> Data.List.findIndices (\x -> x PlutusTx.> n) ||])

findIndicesSpec :: Property
findIndicesSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = findIndicesS (> num) listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ findIndicesProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataFindIndicesProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

filterProgram :: CompiledCode (Integer -> [Integer] -> [Integer])
filterProgram = $$(compile [|| \n -> List.filter (\x -> x PlutusTx.> n) ||])

dataFilterProgram :: CompiledCode (Integer -> Data.List Integer -> Data.List Integer)
dataFilterProgram = $$(compile [|| \n -> Data.List.filter (\x -> x PlutusTx.> n) ||])

filterSpec :: Property
filterSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = filterS (> num) listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ filterProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataFilterProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

mapMaybeProgram :: CompiledCode (Integer -> [Integer] -> [Integer])
mapMaybeProgram =
  $$(compile
  [||
    \n -> PlutusTx.mapMaybe (\x -> if x PlutusTx.> n then Just 1 else Nothing)
  ||])

dataMapMaybeProgram :: CompiledCode (Integer -> Data.List Integer -> Data.List Integer)
dataMapMaybeProgram =
  $$(compile
  [||
    \n -> Data.List.mapMaybe (\x -> if x PlutusTx.> n then Just 1 else Nothing)
  ||])

mapMaybeSpec :: Property
mapMaybeSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected :: ListS Integer
      expected = mapMaybeS (\x -> if x > num then Just 1 else Nothing) listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ mapMaybeProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataMapMaybeProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

anyProgram :: CompiledCode (Integer -> [Integer] -> Bool)
anyProgram = $$(compile [|| \n -> List.any (\x -> x PlutusTx.> n) ||])

dataAnyProgram  :: CompiledCode (Integer -> Data.List Integer -> Bool)
dataAnyProgram = $$(compile [|| \n -> Data.List.any (\x -> x PlutusTx.> n) ||])

anySpec :: Property
anySpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = anyS (> num) listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ anyProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataAnyProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

allProgram :: CompiledCode (Integer -> [Integer] -> Bool)
allProgram = $$(compile [|| \n -> List.all (\x -> x PlutusTx.> n) ||])

dataAllProgram  :: CompiledCode (Integer -> Data.List Integer -> Bool)
dataAllProgram = $$(compile [|| \n -> Data.List.all (\x -> x PlutusTx.> n) ||])

allSpec :: Property
allSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = allS (> num) listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ allProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataAllProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

foldMapProgram :: CompiledCode (Integer -> [Integer] -> Maybe [Integer])
foldMapProgram =
  $$(compile
  [||
    \n -> PlutusTx.foldMap (\x -> if x PlutusTx.> n then Just [x] else Nothing)
  ||])

dataFoldMapProgram :: CompiledCode (Integer -> Data.List Integer -> Maybe [Integer])
dataFoldMapProgram =
  $$(compile
  [||
    \n ->  Data.List.foldMap (\x -> if x PlutusTx.> n then Just [x] else Nothing)
  ||])

foldMapSpec :: Property
foldMapSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = foldMapS (\x -> if x > num then Just [x] else Nothing) listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ foldMapProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataFoldMapProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

mapProgram :: CompiledCode (Integer -> [Integer] -> [Integer])
mapProgram = $$(compile [|| \n -> List.map (\x -> x PlutusTx.+ n) ||])

dataMapProgram :: CompiledCode (Integer -> Data.List Integer -> Data.List Integer)
dataMapProgram = $$(compile [|| \n -> Data.List.map (\x -> x PlutusTx.+ n) ||])

mapSpec :: Property
mapSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = mapS (+ num) listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ mapProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataMapProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

lengthProgram :: CompiledCode ([Integer] -> Integer)
lengthProgram = $$(compile [|| PlutusTx.length ||])

dataLengthProgram :: CompiledCode (Data.List Integer -> Integer)
dataLengthProgram = $$(compile [|| Data.List.length ||])

lengthSpec :: Property
lengthSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = lengthS listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ lengthProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataLengthProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

unconsProgram :: CompiledCode ([Integer] -> Maybe (Integer, [Integer]))
unconsProgram = $$(compile [|| List.uncons ||])

dataUnconsProgram :: CompiledCode (Data.List Integer -> Maybe (Integer, Data.List Integer))
dataUnconsProgram = $$(compile [|| Data.List.uncons ||])

unconsSpec :: Property
unconsSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = unconsS listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ unconsProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    ((fmap . fmap) semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataUnconsProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    ((fmap . fmap) semanticsToDataList expected)

andProgram :: CompiledCode ([Bool] -> Bool)
andProgram = $$(compile [|| PlutusTx.and ||])

dataAndProgram :: CompiledCode (Data.List Bool -> Bool)
dataAndProgram = $$(compile [|| Data.List.and ||])

andSpec :: Property
andSpec = property $ do
  listS <- forAll genListSBool
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = andS listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ andProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataAndProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

orProgram :: CompiledCode ([Bool] -> Bool)
orProgram = $$(compile [|| PlutusTx.or ||])

dataOrProgram :: CompiledCode (Data.List Bool -> Bool)
dataOrProgram = $$(compile [|| Data.List.or ||])

orSpec :: Property
orSpec = property $ do
  listS <- forAll genListSBool
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = Haskell.or list
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ orProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataOrProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

elemProgram :: CompiledCode (Integer -> [Integer] -> Bool)
elemProgram = $$(compile [|| List.elem ||])

dataElemProgram :: CompiledCode (Integer -> Data.List Integer -> Bool)
dataElemProgram = $$(compile [|| Data.List.elem ||])

elemSpec :: Property
elemSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = elemS num listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ elemProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataElemProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

notElemProgram :: CompiledCode (Integer -> [Integer] -> Bool)
notElemProgram = $$(compile [|| List.notElem ||])

dataNotElemProgram :: CompiledCode (Integer -> Data.List Integer -> Bool)
dataNotElemProgram = $$(compile [|| Data.List.notElem ||])

notElemSpec :: Property
notElemSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = notElemS num listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ notElemProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataNotElemProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

foldrProgram :: CompiledCode (Integer -> [Integer] -> Integer)
foldrProgram = $$(compile [|| List.foldr B.subtractInteger ||])

dataFoldrProgram :: CompiledCode (Integer -> Data.List Integer -> Integer)
dataFoldrProgram = $$(compile [|| Data.List.foldr B.subtractInteger ||])

foldrSpec :: Property
foldrSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = foldrS (-) num listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ foldrProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataFoldrProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

foldlProgram :: CompiledCode (Integer -> [Integer] -> Integer)
foldlProgram = $$(compile [|| List.foldl B.subtractInteger ||])

dataFoldlProgram :: CompiledCode (Integer -> Data.List Integer -> Integer)
dataFoldlProgram = $$(compile [|| Data.List.foldl B.subtractInteger ||])

foldlSpec :: Property
foldlSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = foldlS (-) num listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ foldlProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataFoldlProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    expected

concatProgram :: CompiledCode ([[Integer]] -> [Integer])
concatProgram = $$(compile [|| List.concat ||])

dataConcatProgram :: CompiledCode (Data.List (Data.List Integer) -> Data.List Integer)
dataConcatProgram = $$(compile [|| Data.List.concat ||])

concatSpec :: Property
concatSpec = property $ do
  listS <- forAll genListSList
  let list = semanticsToList <$> semanticsToList listS
      dataList = semanticsToDataList $ mapS semanticsToDataList listS
      expected = concatS listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ concatProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataConcatProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

concatMapProgram :: CompiledCode (Integer -> [Integer] -> [Integer])
concatMapProgram = $$(compile [|| \n -> List.concatMap (List.replicate n) ||])

dataConcatMapProgram :: CompiledCode (Integer -> Data.List Integer -> Data.List Integer)
dataConcatMapProgram = $$(compile [|| \n -> Data.List.concatMap (Data.List.replicate n) ||])

concatMapSpec :: Property
concatMapSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = concatMapS (replicateS num) listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ concatMapProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataConcatMapProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)
