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

module AssocMap.Spec where

import Test.Tasty.Extras

import Data.List (nubBy, sort)
import Data.Map.Strict qualified as Map
import Data.These qualified as Haskell
import Hedgehog (Gen, MonadTest, Property, Range, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.Data.AssocMap qualified as Data.AssocMap
import PlutusTx.IsData ()
import PlutusTx.IsData qualified as P
import PlutusTx.Lift (liftCodeDef, makeLift)
import PlutusTx.List qualified as PlutusTx
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.Test.Util.Compiled (cekResultMatchesHaskellValue, compiledCodeToTerm,
                                    unsafeRunTermCek)
import PlutusTx.TH (compile)
import PlutusTx.These (These (..), these)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)


-- | Test the performance and interaction between 'insert', 'delete' and 'lookup'.
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

-- | Test that 'unionWith' is implemented correctly. Due to the nature of 'Map k v',
-- some type errors are only caught when running the PlutusTx compiler on code which uses
-- 'unionWith'.
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

-- | Similar to map2, but uses 'union' instead of 'unionWith'. Evaluating 'map3' and 'map2'
-- should yield the same result.
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

lookupProgram :: CompiledCode (Integer -> AssocMap.Map Integer Integer -> Maybe Integer)
lookupProgram = $$(compile [|| AssocMap.lookup ||])

dataLookupProgram :: CompiledCode (Integer -> Data.AssocMap.Map Integer Integer -> Maybe Integer)
dataLookupProgram = $$(compile [|| Data.AssocMap.lookup ||])

memberProgram :: CompiledCode (Integer -> AssocMap.Map Integer Integer -> Bool)
memberProgram = $$(compile [|| AssocMap.member ||])

dataMemberProgram :: CompiledCode (Integer -> Data.AssocMap.Map Integer Integer -> Bool)
dataMemberProgram = $$(compile [|| Data.AssocMap.member ||])

insertProgram
  :: CompiledCode
    ( Integer
    -> Integer
    -> AssocMap.Map Integer Integer
    -> [(Integer, Integer)]
    )
insertProgram =
  $$(compile
    [|| \k v m ->
      PlutusTx.sort $ AssocMap.toList $ AssocMap.insert k v m
    ||])

dataInsertProgram
  :: CompiledCode
    ( Integer
    -> Integer
    -> Data.AssocMap.Map Integer Integer
    -> [(Integer, Integer)]
    )
dataInsertProgram =
  $$(compile
    [|| \k v m ->
      PlutusTx.sort $ Data.AssocMap.toList $ Data.AssocMap.insert k v m
    ||])

deleteProgram
  :: CompiledCode
    ( Integer
    -> AssocMap.Map Integer Integer
    -> [(Integer, Integer)]
    )
deleteProgram =
  $$(compile
    [|| \k m ->
      PlutusTx.sort $ AssocMap.toList $ AssocMap.delete k m
    ||])

dataDeleteProgram
  :: CompiledCode
    ( Integer
    -> Data.AssocMap.Map Integer Integer
    -> [(Integer, Integer)]
    )
dataDeleteProgram =
  $$(compile
    [|| \k m ->
      PlutusTx.sort $ Data.AssocMap.toList $ Data.AssocMap.delete k m
    ||])

allProgram
  :: CompiledCode
    ( Integer
    -> AssocMap.Map Integer Integer
    -> Bool
    )
allProgram =
  $$(compile [|| \num m -> AssocMap.all (\x -> x PlutusTx.< num) m ||])

dataAllProgram
  :: CompiledCode
    ( Integer
    -> Data.AssocMap.Map Integer Integer
    -> Bool
    )
dataAllProgram =
  $$(compile [|| \num m -> Data.AssocMap.all (\x -> x PlutusTx.< num) m ||])

dataAnyProgram
  :: CompiledCode
    ( Integer
    -> Data.AssocMap.Map Integer Integer
    -> Bool
    )
dataAnyProgram =
  $$(compile [|| \num m -> Data.AssocMap.any (\x -> x PlutusTx.< num) m ||])

keysProgram
  :: CompiledCode
    ( AssocMap.Map Integer Integer
    -> [Integer]
    )
keysProgram =
  $$(compile [|| AssocMap.keys ||])

dataNoDuplicateKeysProgram
  :: CompiledCode
    ( Data.AssocMap.Map Integer Integer
    -> Bool
    )
dataNoDuplicateKeysProgram =
  $$(compile [|| Data.AssocMap.noDuplicateKeys ||])

unionProgram
  :: CompiledCode
    ( AssocMap.Map Integer Integer
    -> AssocMap.Map Integer Integer
    -> [(Integer, These Integer Integer)]
    )
unionProgram =
  $$(compile
    [|| \m1 m2 ->
      PlutusTx.sort $ AssocMap.toList $ AssocMap.union m1 m2
    ||])

dataUnionProgram
  :: CompiledCode
    ( Data.AssocMap.Map Integer Integer
    -> Data.AssocMap.Map Integer Integer
    -> [(Integer, These Integer Integer)]
    )
dataUnionProgram =
  $$(compile
    [|| \m1 m2 ->
      PlutusTx.sort $ Data.AssocMap.toList $ Data.AssocMap.union m1 m2
    ||])

unionWithProgram
  :: CompiledCode
    ( AssocMap.Map Integer Integer
    -> AssocMap.Map Integer Integer
    -> [(Integer, Integer)]
    )
unionWithProgram =
  $$(compile
    [|| \m1 m2 ->
      PlutusTx.sort $ AssocMap.toList $ AssocMap.unionWith (\x _ -> x) m1 m2
    ||])

dataUnionWithProgram
  :: CompiledCode
    ( Data.AssocMap.Map Integer Integer
    -> Data.AssocMap.Map Integer Integer
    -> [(Integer, Integer)]
    )
dataUnionWithProgram =
  $$(compile
    [|| \m1 m2 ->
      PlutusTx.sort $ Data.AssocMap.toList $ Data.AssocMap.unionWith (\x _ -> x) m1 m2
    ||])

encodedDataAssocMap
  :: CompiledCode
    ( Data.AssocMap.Map Integer Integer
    -> PlutusTx.BuiltinData
    )
encodedDataAssocMap = $$(compile [|| P.toBuiltinData ||])

encodedAssocMap
  :: CompiledCode
    ( AssocMap.Map Integer Integer
    -> PlutusTx.BuiltinData
    )
encodedAssocMap = $$(compile [|| P.toBuiltinData ||])

mDecodedDataAssocMap
  :: CompiledCode
    ( Data.AssocMap.Map Integer Integer
    -> PlutusTx.Maybe [(Integer, Integer)]
    )
mDecodedDataAssocMap =
  $$(compile
    [|| fmap (PlutusTx.sort . Data.AssocMap.toList) . P.fromBuiltinData . P.toBuiltinData
    ||])

mDecodedAssocMap
  :: CompiledCode
    ( AssocMap.Map Integer Integer
    -> PlutusTx.Maybe [(Integer, Integer)]
    )
mDecodedAssocMap =
  $$(compile
    [|| fmap (PlutusTx.sort . AssocMap.toList) . P.fromBuiltinData . P.toBuiltinData
    ||])

decodedDataAssocMap
  :: CompiledCode
    ( Data.AssocMap.Map Integer Integer
    -> [(Integer, Integer)]
    )
decodedDataAssocMap =
  $$(compile
    [|| PlutusTx.sort . Data.AssocMap.toList . P.unsafeFromBuiltinData . P.toBuiltinData
    ||])

decodedAssocMap
  :: CompiledCode
    ( AssocMap.Map Integer Integer
    -> [(Integer, Integer)]
    )
decodedAssocMap =
  $$(compile
    [|| PlutusTx.sort . AssocMap.toList . P.unsafeFromBuiltinData . P.toBuiltinData
    ||])

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

mapS :: (a -> b) -> AssocMapS k a -> AssocMapS k b
mapS f (AssocMapS l) = AssocMapS $ map (\(k, v) -> (k, f v)) l

makeLift ''AssocMapS

-- | The semantics of 'union' is based on the 'AssocMap' implementation.
-- The code is duplicated here to avoid any issues if the 'AssocMap' implementation changes.
unionS
  :: AssocMapS Integer Integer
  -> AssocMapS Integer Integer
  -> AssocMapS Integer (Haskell.These Integer Integer)
unionS (AssocMapS ls) (AssocMapS rs) =
  let
    f a b' = case b' of
      Nothing -> Haskell.This a
      Just b  -> Haskell.These a b

    ls' = fmap (\(c, i) -> (c, f i (lookupS c (AssocMapS rs)))) ls

    -- Keeps only those keys which don't appear in the left map.
    rs' = filter (\(c, _) -> not (any (\(c', _) -> c' == c) ls)) rs

    rs'' = fmap (fmap Haskell.That) rs'
   in
    AssocMapS (ls' ++ rs'')

haskellToPlutusThese :: Haskell.These a b -> These a b
haskellToPlutusThese = \case
  Haskell.This a    -> This a
  Haskell.That b    -> That b
  Haskell.These a b -> These a b

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
      expected = lookupS key assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ lookupProgram
        `unsafeApplyCode` (liftCodeDef key)
        `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataLookupProgram
        `unsafeApplyCode` (liftCodeDef key)
        `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    expected

memberSpec :: Property
memberSpec = property $ do
  assocMapS <- forAll genAssocMapS
  key <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = memberS key assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ memberProgram
        `unsafeApplyCode` (liftCodeDef key)
        `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataMemberProgram
        `unsafeApplyCode` (liftCodeDef key)
        `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    expected

insertSpec :: Property
insertSpec = property $ do
  assocMapS <- forAll genAssocMapS
  key <- forAll $ Gen.integral rangeElem
  value <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = sortS $ insertS key value assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ insertProgram
        `unsafeApplyCode` (liftCodeDef key)
        `unsafeApplyCode` (liftCodeDef value)
        `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataInsertProgram
        `unsafeApplyCode` (liftCodeDef key)
        `unsafeApplyCode` (liftCodeDef value)
        `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    expected

deleteSpec :: Property
deleteSpec = property $ do
  assocMapS <- forAll genAssocMapS
  key <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = sortS $ deleteS key assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ deleteProgram
        `unsafeApplyCode` (liftCodeDef key)
        `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataDeleteProgram
        `unsafeApplyCode` (liftCodeDef key)
        `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    expected

allSpec :: Property
allSpec = property $ do
  assocMapS <- forAll genAssocMapS
  num <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = allS (< num) assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ allProgram
        `unsafeApplyCode` (liftCodeDef num)
        `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataAllProgram
        `unsafeApplyCode` (liftCodeDef num)
        `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    expected

anySpec :: Property
anySpec = property $ do
  assocMapS <- forAll genAssocMapS
  num <- forAll $ Gen.integral rangeElem
  let dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = anyS (< num) assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataAnyProgram
        `unsafeApplyCode` (liftCodeDef num)
        `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    expected

keysSpec :: Property
keysSpec = property $ do
  assocMapS <- forAll genAssocMapS
  let assocMap = semanticsToAssocMap assocMapS
      expected = keysS assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ keysProgram
        `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    expected

noDuplicateKeysSpec :: Property
noDuplicateKeysSpec = property $ do
  assocMapS <- forAll genAssocMapS
  let dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = noDuplicateKeysS assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataNoDuplicateKeysProgram
        `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    expected

unionSpec :: Property
unionSpec = property $ do
  -- resizing the generator for performance
  assocMapS1 <- forAll (Gen.resize 20 genAssocMapS)
  assocMapS2 <- forAll (Gen.resize 20 genAssocMapS)
  let assocMap1 = semanticsToAssocMap assocMapS1
      assocMap2 = semanticsToAssocMap assocMapS2
      dataAssocMap1 = semanticsToDataAssocMap assocMapS1
      dataAssocMap2 = semanticsToDataAssocMap assocMapS2
      expected = mapS haskellToPlutusThese $ sortS $ unionS assocMapS1 assocMapS2
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ unionProgram
        `unsafeApplyCode` (liftCodeDef assocMap1)
        `unsafeApplyCode` (liftCodeDef assocMap2)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataUnionProgram
        `unsafeApplyCode` (liftCodeDef dataAssocMap1)
        `unsafeApplyCode` (liftCodeDef dataAssocMap2)
    )
    (===)
    expected

unionWithSpec :: Property
unionWithSpec = property $ do
  -- resizing the generator for performance
  assocMapS1 <- forAll (Gen.resize 20 genAssocMapS)
  assocMapS2 <- forAll (Gen.resize 20 genAssocMapS)
  let assocMap1 = semanticsToAssocMap assocMapS1
      assocMap2 = semanticsToAssocMap assocMapS2
      dataAssocMap1 = semanticsToDataAssocMap assocMapS1
      dataAssocMap2 = semanticsToDataAssocMap assocMapS2
      merge i1 _ = i1
      expected = unionWithS merge assocMapS1 assocMapS2
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ unionWithProgram
        `unsafeApplyCode` (liftCodeDef assocMap1)
        `unsafeApplyCode` (liftCodeDef assocMap2)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ dataUnionWithProgram
        `unsafeApplyCode` (liftCodeDef dataAssocMap1)
        `unsafeApplyCode` (liftCodeDef dataAssocMap2)
    )
    (===)
    expected

builtinDataEncodingSpec :: Property
builtinDataEncodingSpec = property $ do
  assocMapS <- forAll genAssocMapS
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
  unsafeRunTermCek
    ( compiledCodeToTerm
    $ encodedDataAssocMap `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    ===
      unsafeRunTermCek
        ( compiledCodeToTerm
        $ encodedAssocMap `unsafeApplyCode` (liftCodeDef assocMap)
        )
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ mDecodedAssocMap
        `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    (Just assocMapS)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ mDecodedDataAssocMap
        `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    (Just assocMapS)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ decodedAssocMap
        `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm
        $ decodedDataAssocMap
        `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    assocMapS

goldenTests :: TestNested
goldenTests =
  testNested "Budget" . pure $ testNestedGhc
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
