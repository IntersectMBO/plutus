{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ViewPatterns       #-}

{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}

module PlutusTx.SortedMap
    ( SortedMap (..)
    , empty
    , singleton
    , insertOneWith
    , insertOne
    , fromListWith
    , fromList
    , mergeWith
    , MatchResult (..)
    , matchKVs
    , pointwiseEqWith
    , sortFoldMaps
    ) where

import Prelude qualified as Haskell

import PlutusTx.AssocMap qualified as Map
import PlutusTx.Base
import PlutusTx.Ord
import PlutusTx.Prelude

newtype SortedMap k v = UnsafeSortedMap
    { unSortedMap :: [(k, v)]
    } deriving stock (Haskell.Show)

{-# INLINABLE empty #-}
empty :: SortedMap k v
empty = UnsafeSortedMap []

{-# INLINABLE singleton #-}
singleton :: k -> v -> SortedMap k [v]
singleton k v = UnsafeSortedMap [(k, [v])]

{-# INLINE insertOneWith #-}
insertOneWith
    :: forall k v w. Ord k
    => (v -> w -> w) -> (v -> w) -> k -> v -> SortedMap k w -> SortedMap k w
insertOneWith op inj k0 v0 = UnsafeSortedMap . go . unSortedMap where
    go :: [(k, w)] -> [(k, w)]
    go []                  = [(k0, inj v0)]
    go kws@((k, w) : kws') = case k0 `compare` k of
        LT -> (k0, inj v0) : kws
        EQ -> (k0, op v0 w) : kws'
        GT -> (k, w) : go kws'

{-# INLINABLE insertOne #-}
insertOne :: Ord k => k -> v -> SortedMap k [v] -> SortedMap k [v]
insertOne = insertOneWith (:) (: [])

-- TODO: proper mergesort
{-# INLINE fromListWith #-}
fromListWith :: forall k v w. Ord k => (v -> w -> w) -> (v -> w) -> [(k, v)] -> SortedMap k w
fromListWith act inj = go where
    go :: [(k, v)] -> SortedMap k w
    go []             = UnsafeSortedMap []
    go ((k, v) : kvs) = insertOneWith act inj k v $ go kvs

{-# INLINABLE fromList #-}
fromList :: Ord k => [(k, v)] -> SortedMap k [v]
fromList = fromListWith (:) (: [])

{-# INLINE mergeWith #-}
mergeWith
    :: forall k v. Ord k
    => (v -> v -> v) -> SortedMap k v -> SortedMap k v -> SortedMap k v
mergeWith op (UnsafeSortedMap kvs1_0) (UnsafeSortedMap kvs2_0) =
    UnsafeSortedMap $ go kvs1_0 kvs2_0
  where
    go :: [(k, v)] -> [(k, v)] -> [(k, v)]
    go []                kvs2              = kvs2
    go kvs1              []                = kvs1
    go ((k1, v1) : kvs1) ((k2, v2) : kvs2) = case k1 `compare` k2 of
        LT -> (k1, v1) : go kvs1 ((k2, v2) : kvs2)
        EQ -> (k1, op v1 v2) : go kvs1 kvs2
        GT -> (k2, v2) : go ((k1, v1) : kvs1) kvs2

data MatchResult a
    = MatchSuccess
    | MatchFailure a a

{-# INLINABLE matchKVs #-}
matchKVs
    :: forall k v. Ord k
    => (v -> v -> Bool) -> [(k, v)] -> [(k, v)] -> MatchResult (SortedMap k [v])
matchKVs structEqV = go where
    go :: [(k, v)] -> [(k, v)] -> MatchResult (SortedMap k [v])
    go []                      []                      = MatchSuccess
    go []                      kvs2                    = MatchFailure empty (fromList kvs2)
    go kvs1                    []                      = MatchFailure (fromList kvs1) empty
    go kvs1@((k1, v1) : kvs1') kvs2@((k2, v2) : kvs2')
        | k1 == k2 = case go kvs1' kvs2' of
            MatchSuccess -> if structEqV v1 v2
                then MatchSuccess
                else MatchFailure
                    (singleton k1 v1)
                    (singleton k1 v2)
            MatchFailure kvs1'' kvs2'' ->
                MatchFailure
                    (insertOne k1 v1 kvs1'')
                    (insertOne k1 v2 kvs2'')
        | otherwise =
            MatchFailure
                (fromList kvs1)
                (fromList kvs2)

{-# INLINE pointwiseEqWith #-}
pointwiseEqWith
    :: forall k v. Eq k
    => (v -> Bool) -> (v -> v -> Bool) -> SortedMap k v -> SortedMap k v -> Bool
pointwiseEqWith is0 eqV (UnsafeSortedMap kvs01) (UnsafeSortedMap kvs02) = go kvs01 kvs02 where
    go :: [(k, v)] -> [(k, v)] -> Bool
    go []                []                = True
    go []                kvs2              = all (is0 . snd) kvs2
    go kvs1              []                = all (is0 . snd) kvs1
    go ((k1, v1) : kvs1) ((k2, v2) : kvs2) =
        if k1 == k2
            then if go kvs1 kvs2
                then eqV v1 v2
                else False
            else False

{-# INLINE sortFoldMaps #-}
sortFoldMaps
    :: forall k v w. Ord k
    => (w -> w -> w) -> (v -> w -> w) -> (v -> w) -> [Map.Map k v] -> SortedMap k w
sortFoldMaps op act inj = go where
    go :: [Map.Map k v] -> SortedMap k w
    go []                           = empty
    go ((Map.toList -> kvs) : maps) = mergeWith op (fromListWith act inj kvs) (go maps)
