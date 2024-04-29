-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# LANGUAGE FlexibleInstances     #-}

module AssocList.Spec where

import Test.Tasty.Extras

import Control.Monad (when)
import Data.List (nubBy, sort)
import Data.Map.Strict qualified as HMap
import Data.Map.Strict qualified as Map
import Debug.Trace (traceM)
import Hedgehog (Gen, MonadTest, Property, Range, assert, forAll, property, (===))
import Hedgehog.Gen (discard)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.Data.AssocList (AssocList)
import PlutusTx.Data.AssocList qualified as Data.AssocList
import PlutusTx.IsData ()
import PlutusTx.IsData qualified as P
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.TH (compile)
import PlutusTx.These (These (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

goldenTests :: TestNested
goldenTests =
  testNestedGhc
    "Budget"
    [ goldenPirReadable "map1" map1
    , goldenUPlcReadable "map1" map1
    , goldenEvalCekCatch "map1" $ [map1 `unsafeApplyCode` (liftCodeDef 100)]
    , goldenBudget "map1-budget" $ map1 `unsafeApplyCode` (liftCodeDef 100)
    , goldenPirReadable "map2" map2
    , goldenUPlcReadable "map2" map2
    , goldenEvalCekCatch "map2" $ [map2 `unsafeApplyCode` (liftCodeDef 100)]
    , goldenBudget "map2-budget" $ map2 `unsafeApplyCode` (liftCodeDef 100)
    ]

propertyTests :: TestTree
propertyTests =
  testGroup "TESTING Map property tests"
    [ testProperty "safeFromList" safeFromListSpec
    , testProperty "unsafeFromList" unsafeFromListSpec
    , testProperty "lookup" lookupSpec
    , testProperty "member" memberSpec
    , testProperty "insert" insertSpec
    , testProperty "all" allSpec
    , testProperty "any" anySpec
    , testProperty "keys" keysSpec
    , testProperty "uncons" unconsSpec
    , testProperty "unsafeUncons" unsafeUnconsSpec
    , testProperty "noDuplicateKeys" noDuplicateKeysSpec
    , testProperty "delete" deleteSpec
    , testProperty "union" unionSpec
    ]

map1 ::
  CompiledCode
    ( Integer ->
      ( Maybe PlutusTx.BuiltinByteString
      , Maybe PlutusTx.BuiltinByteString
      , Maybe PlutusTx.BuiltinByteString
      , Maybe PlutusTx.BuiltinByteString
      , Maybe PlutusTx.BuiltinByteString
      )
    )
map1 =
  $$( compile
        [||
        \n ->
          let m :: AssocList Integer PlutusTx.BuiltinByteString
              m =
                foldr
                  (\i -> Data.AssocList.insert (n PlutusTx.+ i) (PlutusTx.encodeUtf8 (PlutusTx.show i)))
                  (Data.AssocList.singleton n "0")
                  (PlutusTx.enumFromTo 1 10)
              m' = Data.AssocList.delete (n PlutusTx.+ 5) m
           in ( Data.AssocList.lookup n m
              , Data.AssocList.lookup (n PlutusTx.+ 5) m
              , Data.AssocList.lookup (n PlutusTx.+ 10) m
              , Data.AssocList.lookup (n PlutusTx.+ 20) m
              , Data.AssocList.lookup (n PlutusTx.+ 5) m'
              )
        ||]
    )

map2 :: CompiledCode (Integer -> [(Integer, PlutusTx.BuiltinString)])
map2 =
  $$( compile
        [||
        \n ->
          let m1 =
                Data.AssocList.unsafeFromList
                  [ (n PlutusTx.+ 1, "one")
                  , (n PlutusTx.+ 2, "two")
                  , (n PlutusTx.+ 3, "three")
                  , (n PlutusTx.+ 4, "four")
                  , (n PlutusTx.+ 5, "five")
                  ]
              m2 =
                Data.AssocList.unsafeFromList
                  [ (n PlutusTx.+ 3, "THREE")
                  , (n PlutusTx.+ 4, "FOUR")
                  , (n PlutusTx.+ 6, "SIX")
                  , (n PlutusTx.+ 7, "SEVEN")
                  ]
              m = Data.AssocList.unionWith PlutusTx.appendByteString m1 m2
           in PlutusTx.fmap (\(k, v) -> (k, PlutusTx.decodeUtf8 v)) (Data.AssocList.toList m)
        ||]
    )

newtype AssocListS k v = AssocListS [(k, v)]
  deriving (Show, Eq)

nullS :: AssocListS k v -> Bool
nullS (AssocListS l) = null l

semanticsToAssocMap :: AssocListS k v -> AssocMap.Map k v
semanticsToAssocMap = AssocMap.unsafeFromList . toListS

semanticsToAssocList :: (P.ToData k, P.ToData v) => AssocListS k v -> AssocList k v
semanticsToAssocList = Data.AssocList.unsafeFromList . toListS

assocMapToSemantics :: AssocMap.Map k v -> AssocListS k v
assocMapToSemantics = unsafeFromListS . AssocMap.toList

assocListToSemantics
  :: (P.UnsafeFromData k, P.UnsafeFromData v) => AssocList k v -> AssocListS k v
assocListToSemantics = unsafeFromListS . Data.AssocList.toList

sortS :: (Ord k, Ord v) => AssocListS k v -> AssocListS k v
sortS (AssocListS l) = AssocListS $ sort l

toListS :: AssocListS k v -> [(k, v)]
toListS (AssocListS l) = l

unsafeFromListS :: [(k, v)] -> AssocListS k v
unsafeFromListS = AssocListS

safeFromListS :: Ord k => [(k, v)] -> AssocListS k v
safeFromListS = AssocListS . Map.toList . Map.fromList

lookupS :: Integer -> AssocListS Integer Integer -> Maybe Integer
lookupS k (AssocListS l) = Map.lookup k . Map.fromList $ l

memberS :: Integer -> AssocListS Integer Integer -> Bool
memberS k (AssocListS l) = Map.member k . Map.fromList $ l

insertS :: Integer -> Integer -> AssocListS Integer Integer -> AssocListS Integer Integer
insertS k v (AssocListS l) =
  AssocListS . Map.toList . Map.insert k v . Map.fromList $ l

deleteS :: Integer -> AssocListS Integer Integer -> AssocListS Integer Integer
deleteS k (AssocListS l) =
  AssocListS . Map.toList . Map.delete k . Map.fromList $ l

allS :: (Integer -> Bool) -> AssocListS Integer Integer -> Bool
allS p (AssocListS l) = all (p . snd) l

anyS :: (Integer -> Bool) -> AssocListS Integer Integer -> Bool
anyS p (AssocListS l) = any (p . snd) l

keysS :: AssocListS Integer Integer -> [Integer]
keysS (AssocListS l) = map fst l

unconsS :: AssocListS Integer Integer -> Maybe ((Integer, Integer), AssocListS Integer Integer)
unconsS (AssocListS [])       = Nothing
unconsS (AssocListS (x : xs)) = Just (x, AssocListS xs)

unsafeUnconsS :: AssocListS Integer Integer -> ((Integer, Integer), AssocListS Integer Integer)
unsafeUnconsS (AssocListS [])       = error "unsafeUnconsS: empty list"
unsafeUnconsS (AssocListS (x : xs)) = (x, AssocListS xs)

noDuplicateKeysS :: AssocListS Integer Integer -> Bool
noDuplicateKeysS (AssocListS l) =
  length l == length (nubBy (\(k1, _) (k2, _) -> k1 == k2) l)

genAssocListS :: Gen (AssocListS Integer Integer)
genAssocListS =
  AssocListS . Map.toList <$> Gen.map rangeLength genPair
  where
    genPair :: Gen (Integer, Integer)
    genPair = do
      (,) <$> Gen.integral rangeElem <*> Gen.integral rangeElem

genUnsafeAssocListS :: Gen (AssocListS Integer Integer)
genUnsafeAssocListS = do
  AssocListS <$> Gen.list rangeLength genPair
  where
    genPair :: Gen (Integer, Integer)
    genPair = do
      (,) <$> Gen.integral rangeElem <*> Gen.integral rangeElem

unionS
  :: AssocListS Integer Integer
  -> AssocListS Integer Integer
  -> AssocListS Integer (These Integer Integer)
unionS (AssocListS ls) (AssocListS rs) =
  let
    f a b' = case b' of
      Nothing -> This a
      Just b  -> These a b

    ls' = fmap (\(c, i) -> (c, f i (lookupS c (AssocListS rs)))) ls

    -- Keeps only those keys which don't appear in the left map.
    rs' = filter (\(c, _) -> not (any (\(c', _) -> c' == c) ls)) rs

    rs'' = fmap (fmap That) rs'
   in
    AssocListS (ls' ++ rs'')

class Equivalence l where
  (~~) ::
    ( MonadTest m
    , Show k
    , Show v
    , Ord k
    , Ord v
    , P.UnsafeFromData k
    , P.UnsafeFromData v
    ) => AssocListS k v -> l k v -> m ()

instance Equivalence AssocMap.Map where
  assocListS ~~ assocMap =
    sortS assocListS === sortS (assocMapToSemantics assocMap)

instance Equivalence AssocList where
  assocListS ~~ assocList =
    sortS assocListS === sortS (assocListToSemantics assocList)

rangeElem :: Range Integer
rangeElem = Range.linear 0 100

rangeLength :: Range Int
rangeLength = Range.linear 0 100

safeFromListSpec :: Property
safeFromListSpec = property $ do
  assocListS <- forAll genAssocListS
  let assocMap = AssocMap.safeFromList . toListS $ assocListS
      assocList = Data.AssocList.safeFromList . toListS $ assocListS
  assocListS ~~ assocMap
  assocListS ~~ assocList

unsafeFromListSpec :: Property
unsafeFromListSpec = property $ do
  assocListS <- forAll genAssocListS
  let assocMap = AssocMap.unsafeFromList . toListS $ assocListS
      assocList = Data.AssocList.unsafeFromList . toListS $ assocListS
  assocListS ~~ assocMap
  assocListS ~~ assocList

lookupSpec :: Property
lookupSpec = property $ do
  assocListS <- forAll genAssocListS
  key <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocListS
      assocList = semanticsToAssocList assocListS
  lookupS key assocListS === AssocMap.lookup key assocMap
  lookupS key assocListS === Data.AssocList.lookup key assocList

memberSpec :: Property
memberSpec = property $ do
  assocListS <- forAll genAssocListS
  key <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocListS
      assocList = semanticsToAssocList assocListS
  memberS key assocListS === AssocMap.member key assocMap
  memberS key assocListS === Data.AssocList.member key assocList

insertSpec :: Property
insertSpec = property $ do
  assocListS <- forAll genAssocListS
  key <- forAll $ Gen.integral rangeElem
  value <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocListS
      assocList = semanticsToAssocList assocListS
  insertS key value assocListS ~~ AssocMap.insert key value assocMap
  insertS key value assocListS ~~ Data.AssocList.insert key value assocList

deleteSpec :: Property
deleteSpec = property $ do
  assocListS <- forAll genAssocListS
  key <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocListS
      assocList = semanticsToAssocList assocListS
  deleteS key assocListS ~~ AssocMap.delete key assocMap
  deleteS key assocListS ~~ Data.AssocList.delete key assocList

allSpec :: Property
allSpec = property $ do
  assocListS <- forAll genAssocListS
  num <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocListS
      assocList = semanticsToAssocList assocListS
      predicate x = x < num
  allS predicate assocListS === AssocMap.all predicate assocMap
  allS predicate assocListS === Data.AssocList.all predicate assocList

anySpec :: Property
anySpec = property $ do
  assocListS <- forAll genAssocListS
  num <- forAll $ Gen.integral rangeElem
  let assocList = semanticsToAssocList assocListS
      predicate x = x < num
  anyS predicate assocListS === Data.AssocList.any predicate assocList

keysSpec :: Property
keysSpec = property $ do
  assocListS <- forAll genAssocListS
  let assocMap = semanticsToAssocMap assocListS
  keysS assocListS === AssocMap.keys assocMap

unconsSpec :: Property
unconsSpec = property $ do
  assocListS <- forAll genAssocListS
  let assocList = semanticsToAssocList assocListS
  unconsS assocListS `equiv` Data.AssocList.uncons assocList
  where
    equiv res1 res2 =
      res1 === (fmap . fmap) assocListToSemantics res2

unsafeUnconsSpec :: Property
unsafeUnconsSpec = property $ do
  assocListS <- forAll $ Gen.filter (not . nullS) genAssocListS
  let assocList = semanticsToAssocList assocListS
  unsafeUnconsS assocListS `equiv` Data.AssocList.unsafeUncons assocList
  where
    equiv res1 res2 =
      res1 === fmap assocListToSemantics res2

noDuplicateKeysSpec :: Property
noDuplicateKeysSpec = property $ do
  assocListS <- forAll genAssocListS
  let assocList = semanticsToAssocList assocListS
  noDuplicateKeysS assocListS === Data.AssocList.noDuplicateKeys assocList

unionSpec :: Property
unionSpec = property $ do
  assocListS1 <- forAll genAssocListS
  assocListS2 <- forAll genAssocListS
  let assocMap1 = semanticsToAssocMap assocListS1
      assocMap2 = semanticsToAssocMap assocListS2
      assocList1 = semanticsToAssocList assocListS1
      assocList2 = semanticsToAssocList assocListS2
  unionS assocListS1 assocListS2 ~~ AssocMap.union assocMap1 assocMap2
  unionS assocListS1 assocListS2 ~~ Data.AssocList.union assocList1 assocList2

