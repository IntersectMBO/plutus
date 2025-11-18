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
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
-- CSE is very unstable and produces different output, likely depending on the version of either
-- @unordered-containers@ or @hashable@.
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}

module AssocMap.Semantics where

import Data.List (nubBy, sort)
import Data.Map.Strict qualified as Map
import Data.These qualified as Haskell
import Hedgehog (Gen, MonadTest, Property, Range, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Data.AssocMap qualified as Data.AssocMap
import PlutusTx.IsData ()
import PlutusTx.IsData qualified as P
import PlutusTx.Lift (makeLift)
import PlutusTx.These (These (..))

{-| The semantics of PlutusTx maps and their operations.
The 'PlutusTx' implementations maps ('Data.AssocMap.Map' and 'AssocMap.Map')
are checked against the semantics to ensure correctness. -}
newtype AssocMapS k v = AssocMapS [(k, v)]
  deriving stock (Show, Eq)

semanticsToAssocMap :: AssocMapS k v -> AssocMap.Map k v
semanticsToAssocMap = AssocMap.unsafeFromList . toListS

semanticsToDataAssocMap
  :: (P.ToData k, P.ToData v)
  => AssocMapS k v -> Data.AssocMap.Map k v
semanticsToDataAssocMap = Data.AssocMap.unsafeFromSOPList . toListS

assocMapToSemantics :: AssocMap.Map k v -> AssocMapS k v
assocMapToSemantics = unsafeFromListS . AssocMap.toList

dataAssocMapToSemantics
  :: (P.UnsafeFromData k, P.UnsafeFromData v)
  => Data.AssocMap.Map k v -> AssocMapS k v
dataAssocMapToSemantics = unsafeFromListS . Data.AssocMap.toSOPList

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

elemsS :: AssocMapS Integer Integer -> [Integer]
elemsS (AssocMapS l) = snd <$> l

noDuplicateKeysS :: AssocMapS Integer Integer -> Bool
noDuplicateKeysS (AssocMapS l) =
  length l == length (nubBy (\(k1, _) (k2, _) -> k1 == k2) l)

mapS :: (a -> b) -> AssocMapS k a -> AssocMapS k b
mapS f (AssocMapS l) = AssocMapS $ map (\(k, v) -> (k, f v)) l

filterS
  :: (Integer -> Bool)
  -> AssocMapS Integer Integer
  -> AssocMapS Integer Integer
filterS p (AssocMapS l) =
  AssocMapS $ filter (p . snd) l

mapWithKeyS
  :: (Integer -> Integer -> Integer)
  -> AssocMapS Integer Integer
  -> AssocMapS Integer Integer
mapWithKeyS f (AssocMapS l) =
  AssocMapS . Map.toList . Map.mapWithKey f . Map.fromList $ l

mapMaybeS
  :: (Integer -> Maybe Integer)
  -> AssocMapS Integer Integer
  -> AssocMapS Integer Integer
mapMaybeS f (AssocMapS l) =
  AssocMapS . Map.toList . Map.mapMaybe f . Map.fromList $ l

mapMaybeWithKeyS
  :: (Integer -> Integer -> Maybe Integer)
  -> AssocMapS Integer Integer
  -> AssocMapS Integer Integer
mapMaybeWithKeyS f (AssocMapS l) =
  AssocMapS . Map.toList . Map.mapMaybeWithKey f . Map.fromList $ l

makeLift ''AssocMapS

{-| The semantics of 'union' is based on the 'AssocMap' implementation.
The code is duplicated here to avoid any issues if the 'AssocMap' implementation changes. -}
unionS
  :: AssocMapS Integer Integer
  -> AssocMapS Integer Integer
  -> AssocMapS Integer (Haskell.These Integer Integer)
unionS (AssocMapS ls) (AssocMapS rs) =
  let
    f a b' = case b' of
      Nothing -> Haskell.This a
      Just b -> Haskell.These a b

    ls' = fmap (\(c, i) -> (c, f i (lookupS c (AssocMapS rs)))) ls

    -- Keeps only those keys which don't appear in the left map.
    rs' = filter (\(c, _) -> not (any (\(c', _) -> c' == c) ls)) rs

    rs'' = fmap (fmap Haskell.That) rs'
   in
    AssocMapS (ls' ++ rs'')

haskellToPlutusThese :: Haskell.These a b -> These a b
haskellToPlutusThese = \case
  Haskell.This a -> This a
  Haskell.That b -> That b
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

{-| The 'Equivalence' class is used to define an equivalence relation
between `AssocMapS` and the 'PlutusTx' implementations. -}
class Equivalence l where
  (~~)
    :: ( MonadTest m
       , Show k
       , Show v
       , Ord k
       , Ord v
       , P.UnsafeFromData k
       , P.UnsafeFromData v
       )
    => AssocMapS k v -> l k v -> m ()

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
      dataAssocMap = Data.AssocMap.safeFromSOPList . toListS $ assocMapS
  assocMapS ~~ assocMap
  assocMapS ~~ dataAssocMap

unsafeFromListSpec :: Property
unsafeFromListSpec = property $ do
  assocMapS <- forAll genAssocMapS
  let assocMap = AssocMap.unsafeFromList . toListS $ assocMapS
      dataAssocMap = Data.AssocMap.unsafeFromSOPList . toListS $ assocMapS
  assocMapS ~~ assocMap
  assocMapS ~~ dataAssocMap
