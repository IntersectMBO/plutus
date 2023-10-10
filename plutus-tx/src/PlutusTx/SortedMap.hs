{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ViewPatterns       #-}

{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}

module PlutusTx.SortedMap
    ( SortedMap (..)
    , empty
    , singleton
    , unsafeFromListUnique
    , eqWith
    ) where

import Prelude qualified as Haskell

import PlutusTx.Base
import PlutusTx.Ord
import PlutusTx.Prelude

import Data.Coerce (coerce)

-- | A map from @k@ to @v@ backed by a list that is supposed to be sorted from lowest to highest
-- @k@s with no key duplicated.
newtype SortedMap k v = UnsafeSortedMap
    { unSortedMap :: [(k, v)]
    } deriving stock (Haskell.Show)

{-# INLINEABLE empty #-}
empty :: SortedMap k v
empty = UnsafeSortedMap []

{-# INLINEABLE singleton #-}
singleton :: k -> v -> SortedMap k [v]
singleton k v = UnsafeSortedMap [(k, [v])]

{-# INLINE unsafeInsertOneUnique #-}
-- | Insert a key-value pair into the 'SortedMap' assuming the key isn't already in the map (if it
-- is, the function throws).
unsafeInsertOneUnique :: forall k v. Ord k => k -> v -> SortedMap k v -> SortedMap k v
unsafeInsertOneUnique ~k0 ~v0 = coerce go where
    go :: [(k, v)] -> [(k, v)]
    go []                  = [(k0, v0)]
    go kvs@((k, v) : kvs') =
        case k0 `compare` k of
            LT -> (k0, v0) : kvs
            -- TODO: make this @traceError duplicateElements@.
            EQ -> (k, v0) : kvs'
            GT -> (k, v) : go kvs'

{-# INLINE unsafeFromListUnique #-}
-- | Turn a list into a 'SortedMap' assuming all of its keys are unique (if they are not, the
-- function throws).
unsafeFromListUnique :: forall k v. Ord k => [(k, v)] -> SortedMap k v
unsafeFromListUnique = go where
    go :: [(k, v)] -> SortedMap k v
    go []             = UnsafeSortedMap []
    go ((k, v) : kvs) = unsafeInsertOneUnique k v $ go kvs

-- The pragma trades a bit size for potentially plenty of budget.
{-# INLINE eqWith #-}
-- | Check equality of 'SortedMap's by matching the underlying lists pointwise.
eqWith
    :: forall k v. Eq k
    => (v -> Bool) -> (v -> v -> Bool) -> SortedMap k v -> SortedMap k v -> Bool
eqWith ~is0 ~eqV = coerce go where
    go :: [(k, v)] -> [(k, v)] -> Bool
    go [] []   = True
    go [] kvs2 = all (is0 . snd) kvs2  -- If one of the lists is empty then all elements in the
    go kvs1 [] = all (is0 . snd) kvs1  -- other list need to be zero for lists to be equal.
    go ((k1, v1) : kvs1) ((k2, v2) : kvs2) =
        -- As with 'matchKVs' we check equality of all the keys first and only then check equality
        -- of values.
        if k1 == k2
            then if go kvs1 kvs2
                then eqV v1 v2
                else False
            else False
