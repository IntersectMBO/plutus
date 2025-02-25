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
import PlutusTx.Test.Util.Compiled (cekResultMatchesHaskellValue, compiledCodeToTerm)
import PlutusTx.TH (compile)

import Data.List qualified as Haskell
import Data.Maybe qualified as Haskell

import Hedgehog (Gen, Property, Range, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

-- | Semantics of lists. Used to model the expected behavior of the various
-- PlutusTx list types.
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

genNonEmptyListS :: Gen (ListS Integer)
genNonEmptyListS = ListS <$> Gen.list (Range.linear 1 100) (Gen.integral rangeElem)

genListSBool :: Gen (ListS Bool)
genListSBool = ListS <$> Gen.list rangeLength Gen.bool

genListSList :: Gen (ListS (ListS Integer))
genListSList = ListS <$> Gen.list rangeLength genListS

semanticsToList :: ListS a -> [a]
semanticsToList (ListS l) = l

listToSemantics :: [a] -> ListS a
listToSemantics = ListS

semanticsToDataList :: (ToData a) => ListS a -> Data.List a
semanticsToDataList =
  Data.fromBuiltinList . BI.unsafeDataAsList . B.mkList . fmap toBuiltinData . getListS

dataListToSemantics :: (UnsafeFromData a) => Data.List a -> ListS a
dataListToSemantics (Data.toBuiltinList -> l) = ListS . go $ l
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

allS :: (a -> Bool) -> ListS a -> Bool
allS f (ListS l) = Haskell.all f l

foldMapS :: Monoid m => (a -> m) -> ListS a -> m
foldMapS f (ListS l) = foldMap f l

mapS :: (a -> b) -> ListS a -> ListS b
mapS f (ListS l) = ListS $ Haskell.map f l

lengthS :: ListS a -> Integer
lengthS = fromIntegral . Haskell.length . getListS

unconsS :: ListS a -> Maybe (a, ListS a)
unconsS (ListS [])    = Nothing
unconsS (ListS (h:t)) = Just (h, ListS t)

andS :: ListS Bool -> Bool
andS = Haskell.and . getListS

orS :: ListS Bool -> Bool
orS = Haskell.or . getListS

elemS :: Eq a => a -> ListS a -> Bool
elemS x (ListS l) = Haskell.elem x l

notElemS :: Eq a => a -> ListS a -> Bool
notElemS x (ListS l) = Haskell.notElem x l

foldrS :: (a -> b -> b) -> b -> ListS a -> b
foldrS f z (ListS l) = Haskell.foldr f z l

foldlS :: (b -> a -> b) -> b -> ListS a -> b
foldlS f z (ListS l) = Haskell.foldl f z l

concatS :: ListS (ListS a) -> ListS a
concatS (ListS l) = ListS $ concatMap getListS l

concatMapS :: (a -> ListS b) -> ListS a -> ListS b
concatMapS f (ListS l) = ListS $ concatMap (getListS . f) l

listToMaybeS :: ListS a -> Maybe a
listToMaybeS (ListS [])    = Nothing
listToMaybeS (ListS (h:_)) = Just h

uniqueElementS :: ListS a -> Maybe a
uniqueElementS (ListS [x]) = Just x
uniqueElementS _           = Nothing

findIndexS :: (a -> Bool) -> ListS a -> Maybe Integer
findIndexS f (ListS l) = toInteger <$> Haskell.findIndex f l

indexS :: ListS a -> Integer -> a
indexS (ListS l) i = l Haskell.!! fromIntegral i

revAppendS :: ListS a -> ListS a -> ListS a
revAppendS (ListS l) (ListS l') = ListS $ rev l l'
  where
    rev []     a = a
    rev (x:xs) a = rev xs (x:a)

reverseS :: ListS a -> ListS a
reverseS (ListS l) = ListS $ Haskell.reverse l

zipS :: ListS a -> ListS b -> ListS (a, b)
zipS (ListS l) (ListS l') = ListS $ Haskell.zip l l'

unzipS :: ListS (a, b) -> (ListS a, ListS b)
unzipS (ListS l) =
  let (l1, l2) = Haskell.unzip l
   in (ListS l1, ListS l2)

zipWithS :: (a -> b -> c) -> ListS a -> ListS b -> ListS c
zipWithS f (ListS l) (ListS l') = ListS $ Haskell.zipWith f l l'

headS :: ListS a -> a
headS (ListS l) = Haskell.head l

lastS :: ListS a -> a
lastS (ListS l) = Haskell.last l

tailS :: ListS a -> ListS a
tailS (ListS l) = ListS $ Haskell.tail l

takeS :: Integer -> ListS a -> ListS a
takeS n (ListS l) = ListS $ Haskell.take (fromIntegral n) l

dropS :: Integer -> ListS a -> ListS a
dropS n (ListS l) = ListS $ Haskell.drop (fromIntegral n) l

dropWhileS :: (a -> Bool) -> ListS a -> ListS a
dropWhileS f (ListS l) = ListS $ Haskell.dropWhile f l

takeWhileS :: (a -> Bool) -> ListS a -> ListS a
takeWhileS f (ListS l) = ListS $ Haskell.takeWhile f l

splitAtS :: Integer -> ListS a -> (ListS a, ListS a)
splitAtS n (ListS l) =
  let (l1, l2) = Haskell.splitAt (fromIntegral n) l
   in (ListS l1, ListS l2)

elemByS :: (a -> a -> Bool) -> a -> ListS a -> Bool
elemByS f x (ListS l) = Haskell.any (f x) l

nubByS :: (a -> a -> Bool) -> ListS a -> ListS a
nubByS f (ListS l) = ListS $ Haskell.nubBy f l

nubS :: Eq a => ListS a -> ListS a
nubS (ListS l) = ListS $ Haskell.nub l

replicateS :: Integer -> a -> ListS a
replicateS n x = ListS $ Haskell.replicate (fromIntegral n) x

partitionS :: (a -> Bool) -> ListS a -> (ListS a, ListS a)
partitionS f (ListS l) =
  let (l1, l2) = Haskell.partition f l
   in (ListS l1, ListS l2)

sortBy :: (a -> a -> Ordering) -> ListS a -> ListS a
sortBy f (ListS l) = ListS $ Haskell.sortBy f l

sort :: Ord a => ListS a -> ListS a
sort (ListS l) = ListS $ Haskell.sort l

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
foldrProgram = $$(compile [|| List.foldr B.addInteger ||])

dataFoldrProgram :: CompiledCode (Integer -> Data.List Integer -> Integer)
dataFoldrProgram = $$(compile [|| Data.List.foldr B.addInteger ||])

foldrSpec :: Property
foldrSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = foldrS (+) num listS
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
foldlProgram = $$(compile [|| List.foldl B.addInteger ||])

dataFoldlProgram :: CompiledCode (Integer -> Data.List Integer -> Integer)
dataFoldlProgram = $$(compile [|| Data.List.foldl B.addInteger ||])

foldlSpec :: Property
foldlSpec = property $ do
  listS <- forAll genListS
  num <- forAll $ Gen.integral rangeElem
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = foldlS (+) num listS
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

concatMapProgram :: CompiledCode ([Integer] -> [Integer])
concatMapProgram = $$(compile [|| List.concatMap (List.replicate 2) ||])

dataConcatMapProgram :: CompiledCode (Data.List Integer -> Data.List Integer)
dataConcatMapProgram = $$(compile [|| Data.List.concatMap (Data.List.replicate 2) ||])

concatMapSpec :: Property
concatMapSpec = property $ do
  listS <- forAll genListS
  let list = semanticsToList listS
      dataList = semanticsToDataList listS
      expected = concatMapS (replicateS 2) listS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ concatMapProgram
        `unsafeApplyCode` liftCodeDef list
    )
    (===)
    (semanticsToList expected)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataConcatMapProgram
        `unsafeApplyCode` liftCodeDef dataList
    )
    (===)
    (semanticsToDataList expected)

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

findIndexProgram :: CompiledCode (Integer -> [Integer] -> Maybe Integer)
findIndexProgram = $$(compile [|| \num -> List.findIndex (== num) ||])

dataFindIndexProgram :: CompiledCode (Integer -> Data.List Integer -> Maybe Integer)
dataFindIndexProgram = $$(compile [|| \num -> Data.List.findIndex (== num) ||])

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

-- this is insanely slow
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

propertyTests :: TestTree
propertyTests =
  testGroup "List property tests"
    [ testProperty "areInverses" areInversesSpec
    , testProperty "toSOP" toSOPSpec
    , testProperty "fromSOP" fromSOPSpec
    , testProperty "append" appendSpec
    , testProperty "find" findSpec
    , testProperty "findIndices" findIndicesSpec
    , testProperty "filter" filterSpec
    , testProperty "mapMaybe" mapMaybeSpec
    , testProperty "any" anySpec
    , testProperty "all" allSpec
    , testProperty "foldMap" foldMapSpec
    , testProperty "map" mapSpec
    , testProperty "length" lengthSpec
    , testProperty "uncons" unconsSpec
    , testProperty "and" andSpec
    , testProperty "or" orSpec
    , testProperty "elem" elemSpec
    , testProperty "notElem" notElemSpec
    , testProperty "foldr" foldrSpec
    , testProperty "foldl" foldlSpec
    , testProperty "concat" concatSpec
    , testProperty "concatMap" concatMapSpec
    , testProperty "listToMaybe" listToMaybeSpec
    , testProperty "uniqueElement" uniqueElementSpec
    , testProperty "findIndex" findIndexSpec
    , testProperty "index" indexSpec
    , testProperty "revAppend" revAppendSpec
    ]
