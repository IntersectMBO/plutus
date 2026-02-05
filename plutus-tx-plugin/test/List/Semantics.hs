{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-warning-flags #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

module List.Semantics where

import PlutusTx.Builtins as B
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Data.List qualified as Data
import PlutusTx.IsData
import PlutusTx.Lift (makeLift)

import Data.List qualified as Haskell
import Data.Maybe qualified as Haskell

import Hedgehog (Gen, Property, Range, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

{-| Semantics of lists. Used to model the expected behavior of the various
PlutusTx list types. -}
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

genListSPair :: Gen (ListS (Integer, Integer))
genListSPair =
  ListS
    <$> Gen.list
      rangeLength
      ((,) <$> Gen.integral rangeElem <*> Gen.integral rangeElem)

semanticsToList :: ListS a -> [a]
semanticsToList (ListS l) = l

listToSemantics :: [a] -> ListS a
listToSemantics = ListS

semanticsToDataList :: ToData a => ListS a -> Data.List a
semanticsToDataList =
  Data.fromBuiltinList . BI.unsafeDataAsList . B.mkList . fmap toBuiltinData . getListS

semanticsToDataListIntPair :: ListS (Integer, Integer) -> Data.List (Integer, Integer)
semanticsToDataListIntPair =
  Data.fromBuiltinList . BI.unsafeDataAsList . B.mkList . fmap toBuiltinData . getListS

dataListToSemantics :: UnsafeFromData a => Data.List a -> ListS a
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
unconsS (ListS []) = Nothing
unconsS (ListS (h : t)) = Just (h, ListS t)

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
listToMaybeS (ListS []) = Nothing
listToMaybeS (ListS (h : _)) = Just h

uniqueElementS :: ListS a -> Maybe a
uniqueElementS (ListS [x]) = Just x
uniqueElementS _ = Nothing

findIndexS :: (a -> Bool) -> ListS a -> Maybe Integer
findIndexS f (ListS l) = toInteger <$> Haskell.findIndex f l

indexS :: ListS a -> Integer -> a
indexS (ListS l) i = l Haskell.!! fromIntegral i

revAppendS :: ListS a -> ListS a -> ListS a
revAppendS (ListS l) (ListS l') = ListS $ rev l l'
  where
    rev [] a = a
    rev (x : xs) a = rev xs (x : a)

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

elemByS :: forall a. (a -> a -> Bool) -> a -> ListS a -> Bool
elemByS eq y (ListS l) = go l
  where
    go :: [a] -> Bool
    go [] = False
    go (x : xs) = x `eq` y || go xs

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
