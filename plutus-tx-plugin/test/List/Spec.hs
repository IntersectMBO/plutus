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
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
-- CSE is very unstable and produces different output, likely depending on the version of either
-- @unordered-containers@ or @hashable@.
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}

module List.Spec where

import PlutusTx.Builtins as B
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Code
import PlutusTx.Data.List qualified as Data
import PlutusTx.Data.List qualified as Data.List
import PlutusTx.IsData
import PlutusTx.Lift (liftCodeDef, makeLift)
import PlutusTx.List qualified as List
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test.Util.Compiled (cekResultMatchesHaskellValue, compiledCodeToTerm,
                                    unsafeRunTermCek)
import PlutusTx.TH (compile)

import Data.List qualified as Haskell
import Data.Maybe qualified as Haskell

import Hedgehog (Gen, MonadTest, Property, Range, forAll, property, test, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

newtype ListS a = ListS {getListS :: [a]}
  deriving stock (Show, Eq)
  deriving newtype (Semigroup, Monoid)

makeLift ''ListS

rangeElem :: Range Integer
rangeElem = Range.linear 0 100

rangeLength :: Range Int
rangeLength = Range.linear 0 100

genListS :: Gen (ListS Integer)
genListS = ListS <$> Gen.list rangeLength (Gen.integral rangeElem)

semanticsToList :: ListS a -> [a]
semanticsToList (ListS l) = l

listToSemantics :: [a] -> ListS a
listToSemantics = ListS

semanticsToDataList :: (ToData a) => ListS a -> Data.List a
semanticsToDataList =
  Data.List . BI.unsafeDataAsList . B.mkList . fmap toBuiltinData . getListS

dataListToSemantics :: (UnsafeFromData a) => Data.List a -> ListS a
dataListToSemantics (Data.List l) = ListS . go $ l
  where
    go = B.caseList' [] (\h t -> unsafeFromBuiltinData h : go t)

areInversesSpec :: Property
areInversesSpec = property $ do
  listS <- forAll genListS
  let listS' = listToSemantics (semanticsToList listS)
  listS === listS'

dataAreInversesSpec :: Property
dataAreInversesSpec = property $ do
  listS <- forAll genListS
  let listS' = dataListToSemantics (semanticsToDataList listS)
  listS === listS'

appendS :: ListS a -> ListS a -> ListS a
appendS (ListS l) (ListS l') = ListS (l ++ l')

findS :: (a -> Bool) -> ListS a -> Maybe a
findS f (ListS l) = Haskell.find f l

findIndicesS :: (a -> Bool) -> ListS a -> ListS Integer
findIndicesS f (ListS l) = ListS $ toInteger <$> Haskell.findIndices f l

filterS :: (a -> Bool) -> ListS a -> ListS a
filterS f (ListS l) = ListS $ Haskell.filter f l

mapMaybeS :: (a -> Maybe b) -> ListS a -> ListS b
mapMaybeS f (ListS l) = ListS $ Haskell.mapMaybe f l

anyS :: (a -> Bool) -> ListS a -> Bool
anyS f (ListS l) = Haskell.any f l

foldMapS :: Monoid m => (a -> m) -> ListS a -> m
foldMapS f (ListS l) = foldMap f l

mapS :: (a -> b) -> ListS a -> ListS b
mapS f (ListS l) = ListS $ Haskell.map f l

lengthS :: ListS a -> Integer
lengthS = fromIntegral . Haskell.length . getListS

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

dataFindIndicesProgram :: CompiledCode (Integer -> Data.List Integer -> [Integer])
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
    (semanticsToList expected)

filterProgram :: CompiledCode (Integer -> [Integer] -> [Integer])
filterProgram = $$(compile [|| \n -> List.filter (\x -> x PlutusTx.> n) ||])

dataFilterProgram :: CompiledCode (Integer -> Data.List Integer -> [Integer])
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
    (semanticsToList expected)

mapMaybeProgram :: CompiledCode (Integer -> [Integer] -> [Integer])
mapMaybeProgram =
  $$(compile
  [||
    \n -> PlutusTx.mapMaybe (\x -> if x PlutusTx.> n then Just 1 else Nothing)
  ||])

dataMapMaybeProgram :: CompiledCode (Integer -> Data.List Integer -> [Integer])
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
    (semanticsToList expected)

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

propertyTests :: TestTree
propertyTests =
  testGroup "TESTING List property tests"
    [ testProperty "areInverses" areInversesSpec
    , testProperty "toSOP" toSOPSpec
    , testProperty "fromSOP" fromSOPSpec
    , testProperty "append" appendSpec
    , testProperty "find" findSpec
    , testProperty "findIndices" findIndicesSpec
    , testProperty "filter" filterSpec
    , testProperty "mapMaybe" mapMaybeSpec
    , testProperty "any" anySpec
    , testProperty "foldMap" foldMapSpec
    , testProperty "map" mapSpec
    , testProperty "length" lengthSpec
    ]
