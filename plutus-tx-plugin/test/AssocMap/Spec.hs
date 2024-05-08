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

module AssocMap.Spec where

import Test.Tasty.Extras

import Data.List (nubBy, sort)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust)
import Hedgehog (Gen, MonadTest, Property, Range, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.Data.AssocMap qualified as Data.AssocMap
import PlutusTx.IsData ()
import PlutusTx.IsData qualified as P
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.TH (compile)
import PlutusTx.These (These (..), these)
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
    , goldenPirReadable "map3" map2
    , goldenUPlcReadable "map3" map2
    , goldenEvalCekCatch "map3" $ [map2 `unsafeApplyCode` (liftCodeDef 100)]
    , goldenBudget "map3-budget" $ map2 `unsafeApplyCode` (liftCodeDef 100)
    ]

propertyTests :: TestTree
propertyTests =
  testGroup "Map property tests"
    [ testProperty "safeFromList" safeFromListSpec
    , testProperty "unsafeFromList" unsafeFromListSpec
    , testProperty "lookup" lookupSpec
    , testProperty "member" memberSpec
    , testProperty "insert" insertSpec
    , testProperty "all" allSpec
    , testProperty "any" anySpec
    , testProperty "keys" keysSpec
    , testProperty "noDuplicateKeys" noDuplicateKeysSpec
    , testProperty "delete" deleteSpec
    , testProperty "union" unionSpec
    , testProperty "unionWith" unionWithSpec
    , testProperty "builtinDataEncoding" builtinDataEncodingSpec
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
          let m :: Data.AssocMap.Map Integer PlutusTx.BuiltinByteString
              m =
                foldr
                  (\i ->
                    Data.AssocMap.insert
                      (n PlutusTx.+ i)
                      (PlutusTx.encodeUtf8 (PlutusTx.show i))
                  )
                  (Data.AssocMap.singleton n "0")
                  (PlutusTx.enumFromTo 1 10)
              m' = Data.AssocMap.delete (n PlutusTx.+ 5) m
           in ( Data.AssocMap.lookup n m
              , Data.AssocMap.lookup (n PlutusTx.+ 5) m
              , Data.AssocMap.lookup (n PlutusTx.+ 10) m
              , Data.AssocMap.lookup (n PlutusTx.+ 20) m
              , Data.AssocMap.lookup (n PlutusTx.+ 5) m'
              )
        ||]
    )

map2 :: CompiledCode (Integer -> [(Integer, PlutusTx.BuiltinString)])
map2 =
  $$( compile
        [||
        \n ->
          let m1 =
                Data.AssocMap.unsafeFromList
                  [ (n PlutusTx.+ 1, "one")
                  , (n PlutusTx.+ 2, "two")
                  , (n PlutusTx.+ 3, "three")
                  , (n PlutusTx.+ 4, "four")
                  , (n PlutusTx.+ 5, "five")
                  ]
              m2 =
                Data.AssocMap.unsafeFromList
                  [ (n PlutusTx.+ 3, "THREE")
                  , (n PlutusTx.+ 4, "FOUR")
                  , (n PlutusTx.+ 6, "SIX")
                  , (n PlutusTx.+ 7, "SEVEN")
                  ]
              m = Data.AssocMap.unionWith PlutusTx.appendByteString m1 m2
           in PlutusTx.fmap (\(k, v) -> (k, PlutusTx.decodeUtf8 v)) (Data.AssocMap.toList m)
        ||]
    )

map3 :: CompiledCode (Integer -> [(Integer, PlutusTx.BuiltinString)])
map3 =
  $$( compile
        [||
        \n ->
          let m1 =
                Data.AssocMap.unsafeFromList
                  [ (n PlutusTx.+ 1, "one")
                  , (n PlutusTx.+ 2, "two")
                  , (n PlutusTx.+ 3, "three")
                  , (n PlutusTx.+ 4, "four")
                  , (n PlutusTx.+ 5, "five")
                  ]
              m2 =
                Data.AssocMap.unsafeFromList
                  [ (n PlutusTx.+ 3, "THREE")
                  , (n PlutusTx.+ 4, "FOUR")
                  , (n PlutusTx.+ 6, "SIX")
                  , (n PlutusTx.+ 7, "SEVEN")
                  ]
              m = Data.AssocMap.union m1 m2
              f = these id id PlutusTx.appendByteString
           in PlutusTx.fmap (\(k, v) -> (k, PlutusTx.decodeUtf8 (f v))) (Data.AssocMap.toList m)
        ||]
    )

-- | The semantics of PlutusTx maps and their operations.
-- The 'PlutusTx' implementations maps ('Data.AssocMap.Map' and 'AssocMap.Map')
-- are checked against the semantics to ensure correctness.
newtype AssocMapS k v = AssocMapS [(k, v)]
  deriving stock (Show, Eq)

semanticsToAssocMap :: AssocMapS k v -> AssocMap.Map k v
semanticsToAssocMap = AssocMap.unsafeFromList . toListS

semanticsToDataAssocMap
  :: (P.ToData k, P.ToData v)
  => AssocMapS k v -> Data.AssocMap.Map k v
semanticsToDataAssocMap = Data.AssocMap.unsafeFromList . toListS

assocMapToSemantics :: AssocMap.Map k v -> AssocMapS k v
assocMapToSemantics = unsafeFromListS . AssocMap.toList

dataAssocMapToSemantics
  :: (P.UnsafeFromData k, P.UnsafeFromData v)
  => Data.AssocMap.Map k v -> AssocMapS k v
dataAssocMapToSemantics = unsafeFromListS . Data.AssocMap.toList

nullS :: AssocMapS k v -> Bool
nullS (AssocMapS l) = null l

sortS :: (Ord k, Ord v) => AssocMapS k v -> AssocMapS k v
sortS (AssocMapS l) = AssocMapS $ sort l

toListS :: AssocMapS k v -> [(k, v)]
toListS (AssocMapS l) = l

unsafeFromListS :: [(k, v)] -> AssocMapS k v
unsafeFromListS = AssocMapS

safeFromListS :: Ord k => [(k, v)] -> AssocMapS k v
safeFromListS = AssocMapS . Map.toList . Map.fromList

lookupS :: Integer -> AssocMapS Integer Integer -> Maybe Integer
lookupS k (AssocMapS l) = Map.lookup k . Map.fromList $ l

memberS :: Integer -> AssocMapS Integer Integer -> Bool
memberS k (AssocMapS l) = Map.member k . Map.fromList $ l

insertS :: Integer -> Integer -> AssocMapS Integer Integer -> AssocMapS Integer Integer
insertS k v (AssocMapS l) =
  AssocMapS . Map.toList . Map.insert k v . Map.fromList $ l

deleteS :: Integer -> AssocMapS Integer Integer -> AssocMapS Integer Integer
deleteS k (AssocMapS l) =
  AssocMapS . Map.toList . Map.delete k . Map.fromList $ l

allS :: (Integer -> Bool) -> AssocMapS Integer Integer -> Bool
allS p (AssocMapS l) = all (p . snd) l

anyS :: (Integer -> Bool) -> AssocMapS Integer Integer -> Bool
anyS p (AssocMapS l) = any (p . snd) l

keysS :: AssocMapS Integer Integer -> [Integer]
keysS (AssocMapS l) = map fst l

noDuplicateKeysS :: AssocMapS Integer Integer -> Bool
noDuplicateKeysS (AssocMapS l) =
  length l == length (nubBy (\(k1, _) (k2, _) -> k1 == k2) l)

-- | The semantics of 'union' is based on the 'AssocMap' implementation.
-- The code is duplicated here to avoid any issues if the 'AssocMap' implementation changes.
unionS
  :: AssocMapS Integer Integer
  -> AssocMapS Integer Integer
  -> AssocMapS Integer (These Integer Integer)
unionS (AssocMapS ls) (AssocMapS rs) =
  let
    f a b' = case b' of
      Nothing -> This a
      Just b  -> These a b

    ls' = fmap (\(c, i) -> (c, f i (lookupS c (AssocMapS rs)))) ls

    -- Keeps only those keys which don't appear in the left map.
    rs' = filter (\(c, _) -> not (any (\(c', _) -> c' == c) ls)) rs

    rs'' = fmap (fmap That) rs'
   in
    AssocMapS (ls' ++ rs'')

unionWithS
  :: (Integer -> Integer -> Integer)
  -> AssocMapS Integer Integer
  -> AssocMapS Integer Integer
  -> AssocMapS Integer Integer
unionWithS merge (AssocMapS ls) (AssocMapS rs) =
  AssocMapS
  . Map.toList
  $ Map.unionWith merge (Map.fromList ls) (Map.fromList rs)

genAssocMapS :: Gen (AssocMapS Integer Integer)
genAssocMapS =
  AssocMapS . Map.toList <$> Gen.map rangeLength genPair
  where
    genPair :: Gen (Integer, Integer)
    genPair = do
      (,) <$> Gen.integral rangeElem <*> Gen.integral rangeElem

genUnsafeAssocMapS :: Gen (AssocMapS Integer Integer)
genUnsafeAssocMapS = do
  AssocMapS <$> Gen.list rangeLength genPair
  where
    genPair :: Gen (Integer, Integer)
    genPair = do
      (,) <$> Gen.integral rangeElem <*> Gen.integral rangeElem

-- | The 'Equivalence' class is used to define an equivalence relation
-- between `AssocMapS` and the 'PlutusTx' implementations.
class Equivalence l where
  (~~) ::
    ( MonadTest m
    , Show k
    , Show v
    , Ord k
    , Ord v
    , P.UnsafeFromData k
    , P.UnsafeFromData v
    ) => AssocMapS k v -> l k v -> m ()

-- | An `AssocMap.Map` is equivalent to an `AssocMapS` if they have the same elements.
instance Equivalence AssocMap.Map where
  assocMapS ~~ assocMap =
    sortS assocMapS === sortS (assocMapToSemantics assocMap)

-- | An `Data.AssocMap.Map` is equivalent to an `AssocMapS` if they have the same elements.
instance Equivalence Data.AssocMap.Map where
  assocMapS ~~ dataAssocMap =
    sortS assocMapS === sortS (dataAssocMapToSemantics dataAssocMap)

rangeElem :: Range Integer
rangeElem = Range.linear 0 100

rangeLength :: Range Int
rangeLength = Range.linear 0 100

safeFromListSpec :: Property
safeFromListSpec = property $ do
  assocMapS <- forAll genAssocMapS
  let assocMap = AssocMap.safeFromList . toListS $ assocMapS
      dataAssocMap = Data.AssocMap.safeFromList . toListS $ assocMapS
  assocMapS ~~ assocMap
  assocMapS ~~ dataAssocMap

unsafeFromListSpec :: Property
unsafeFromListSpec = property $ do
  assocMapS <- forAll genAssocMapS
  let assocMap = AssocMap.unsafeFromList . toListS $ assocMapS
      dataAssocMap = Data.AssocMap.unsafeFromList . toListS $ assocMapS
  assocMapS ~~ assocMap
  assocMapS ~~ dataAssocMap

lookupSpec :: Property
lookupSpec = property $ do
  assocMapS <- forAll genAssocMapS
  key <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
  lookupS key assocMapS === AssocMap.lookup key assocMap
  lookupS key assocMapS === Data.AssocMap.lookup key dataAssocMap

memberSpec :: Property
memberSpec = property $ do
  assocMapS <- forAll genAssocMapS
  key <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
  memberS key assocMapS === AssocMap.member key assocMap
  memberS key assocMapS === Data.AssocMap.member key dataAssocMap

insertSpec :: Property
insertSpec = property $ do
  assocMapS <- forAll genAssocMapS
  key <- forAll $ Gen.integral rangeElem
  value <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
  insertS key value assocMapS ~~ AssocMap.insert key value assocMap
  insertS key value assocMapS ~~ Data.AssocMap.insert key value dataAssocMap

deleteSpec :: Property
deleteSpec = property $ do
  assocMapS <- forAll genAssocMapS
  key <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
  deleteS key assocMapS ~~ AssocMap.delete key assocMap
  deleteS key assocMapS ~~ Data.AssocMap.delete key dataAssocMap

allSpec :: Property
allSpec = property $ do
  assocMapS <- forAll genAssocMapS
  num <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      predicate x = x < num
  allS predicate assocMapS === AssocMap.all predicate assocMap
  allS predicate assocMapS === Data.AssocMap.all predicate dataAssocMap

anySpec :: Property
anySpec = property $ do
  assocMapS <- forAll genAssocMapS
  num <- forAll $ Gen.integral rangeElem
  let dataAssocMap = semanticsToDataAssocMap assocMapS
      predicate x = x < num
  anyS predicate assocMapS === Data.AssocMap.any predicate dataAssocMap

keysSpec :: Property
keysSpec = property $ do
  assocMapS <- forAll genAssocMapS
  let assocMap = semanticsToAssocMap assocMapS
  keysS assocMapS === AssocMap.keys assocMap

noDuplicateKeysSpec :: Property
noDuplicateKeysSpec = property $ do
  assocMapS <- forAll genAssocMapS
  let dataAssocMap = semanticsToDataAssocMap assocMapS
  noDuplicateKeysS assocMapS === Data.AssocMap.noDuplicateKeys dataAssocMap

unionSpec :: Property
unionSpec = property $ do
  assocMapS1 <- forAll genAssocMapS
  assocMapS2 <- forAll genAssocMapS
  let assocMap1 = semanticsToAssocMap assocMapS1
      assocMap2 = semanticsToAssocMap assocMapS2
      dataAssocMap1 = semanticsToDataAssocMap assocMapS1
      dataAssocMap2 = semanticsToDataAssocMap assocMapS2
  unionS assocMapS1 assocMapS2 ~~ AssocMap.union assocMap1 assocMap2
  unionS assocMapS1 assocMapS2 ~~ Data.AssocMap.union dataAssocMap1 dataAssocMap2

unionWithSpec :: Property
unionWithSpec = property $ do
  assocMapS1 <- forAll genAssocMapS
  assocMapS2 <- forAll genAssocMapS
  let assocMap1 = semanticsToAssocMap assocMapS1
      assocMap2 = semanticsToAssocMap assocMapS2
      dataAssocMap1 = semanticsToDataAssocMap assocMapS1
      dataAssocMap2 = semanticsToDataAssocMap assocMapS2
      merge i1 _ = i1
  unionWithS merge assocMapS1 assocMapS2 ~~ AssocMap.unionWith merge assocMap1 assocMap2
  unionWithS merge assocMapS1 assocMapS2
    ~~ Data.AssocMap.unionWith merge dataAssocMap1 dataAssocMap2

builtinDataEncodingSpec :: Property
builtinDataEncodingSpec = property $ do
  assocMapS <- forAll genAssocMapS
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      encodedDataAssocMap = P.toBuiltinData dataAssocMap
      encodedAssocMap = P.toBuiltinData assocMap
      mDecodedDataAssocMap :: Maybe (Data.AssocMap.Map Integer Integer)
      mDecodedDataAssocMap = P.fromBuiltinData encodedDataAssocMap
      mDecodedAssocMap :: Maybe (AssocMap.Map Integer Integer)
      mDecodedAssocMap = P.fromBuiltinData encodedAssocMap
      decodedDataAssocMap :: Data.AssocMap.Map Integer Integer
      decodedDataAssocMap = P.unsafeFromBuiltinData encodedDataAssocMap
      decodedAssocMap :: AssocMap.Map Integer Integer
      decodedAssocMap = P.unsafeFromBuiltinData encodedAssocMap
  encodedDataAssocMap === encodedAssocMap
  assocMapS ~~ fromJust mDecodedAssocMap
  assocMapS ~~ fromJust mDecodedDataAssocMap
  assocMapS ~~ decodedAssocMap
  assocMapS ~~ decodedDataAssocMap
