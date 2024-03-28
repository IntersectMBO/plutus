{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.DataMap where

import PlutusTx.AsData qualified as AsData
import PlutusTx.DataList (List, pattern Cons, pattern Nil)
import PlutusTx.DataList qualified as List
import PlutusTx.DataPair
import PlutusTx.DataThese
import PlutusTx.IsData qualified as P
import PlutusTx.Prelude hiding (fst, map, snd)
import Prelude qualified as H

AsData.asData
  [d|
    data Map k v = Map (List (Pair k v))
      deriving newtype (P.ToData, P.FromData, P.UnsafeFromData)
  |]

empty :: (DataElem k, DataElem v) => Map k v
empty = Map Nil

lookup :: (DataElem k, DataElem v, Eq k) => k -> Map k v -> Maybe v
lookup k (Map l) = go l
  where
    go Nil = Nothing
    go (Cons x xs)
        | k == fst x = Just . snd $ x
        | otherwise = go xs

member :: (DataElem k, DataElem v, Eq k) => k -> Map k v -> Bool
member k m =
    case lookup k m of
        Just _  -> True
        Nothing -> False

toList :: (DataElem k, DataElem v) => Map k v -> List (Pair k v)
toList (Map l) = l

unsafeFromList :: (DataElem k, DataElem v) => List (Pair k v) -> Map k v
unsafeFromList = Map

delete :: (DataElem k, DataElem v, Eq k) => k -> Map k v -> Map k v
delete key (Map l) = Map $ go l
  where
    go Nil = Nil
    go (Cons (Pair k v) xs)
        | key == k = xs
        | otherwise = Cons (Pair k v) (go xs)

insert :: (DataElem k, DataElem v, Eq k) => k -> v -> Map k v -> Map k v
insert key val (Map l) = Map $ go l
  where
    go Nil = Cons (Pair key val) Nil
    go (Cons (Pair k v) xs)
        | key == k = Cons (Pair key val) (go xs)
        | otherwise = Cons (Pair k v) (go xs)

null :: (DataElem k, DataElem v) => Map k v -> Bool
null (Map Nil) = True
null _         = False

keys :: (DataElem k, DataElem v) => Map k v -> List k
keys (Map l) = List.map fst l

singleton :: (DataElem k, DataElem v) => k -> v -> Map k v
singleton k v = Map $ Cons (Pair k v) Nil

union
    :: (DataElem k, DataElem v1, DataElem v2)
    => Map k v1 -> Map k v2 -> Map k (These v1 v2)
union = H.undefined

all :: (DataElem k, DataElem v) => (v -> Bool) -> Map k v -> Bool
all = H.undefined

mapThese
    :: (DataElem k, DataElem v1, DataElem v2)
    => (v1 -> These v1 v2) -> Map k v1 -> (Map k v1, Map k v2)
mapThese = H.undefined

map
    :: (DataElem k, DataElem v1, DataElem v2)
    => (v1 -> v2) -> Map k v1 -> Map k v2
map = H.undefined
