{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
-- | This is like `PlutusTx.AssocMap` but with the extra invariant that the entries are kept
-- sorted on the KEYS upon construction, insertion, and deletion.
module PlutusTx.SortedMap
    ( SortedMap
    , empty
    , insert
    , delete
    , lookup
    , minViewWithKey
    , isSorted
    , isValid
    -- * conversion from/to AssocMap
    , sort
    , sort'
    , fromMapSafe
    , fromMapUnsafe
    , toMap
    -- * conversion from/to List
    , fromListSafe
    , fromListUnsafe
    , toList
    ) where

import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Base as Tx
import PlutusTx.Bool as Tx
import PlutusTx.Eq as Tx
import PlutusTx.Functor as Tx
import PlutusTx.Lift as Tx
import PlutusTx.List qualified as Tx
import PlutusTx.Ord as Tx

import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax as TH
import Prelude qualified as Haskell

newtype SortedMap k v = SortedMap { unSortedMap :: AssocMap.Map k v }
  deriving stock (Generic, Haskell.Eq, Haskell.Show, TH.Lift)
  deriving newtype (Tx.Eq, Tx.Ord)

{-# INLINABLE sort' #-}
-- | Alternative sort implementation by using insertion sort
sort' :: (Tx.Ord k) => AssocMap.Map k v -> SortedMap k v
sort' = SortedMap . AssocMap.fromList . Tx.foldr insertInternal [] . AssocMap.toList

{-# INLINABLE sort #-}
-- | Sorting by using merge sort.
--
-- TODO: test what happens upon duplicates (assocmap may contain duplicates...).
sort :: (Tx.Ord k) => AssocMap.Map k v -> SortedMap k v
sort = SortedMap
     . AssocMap.fromList
     . Tx.sortBy (\ l r -> fst l `compare` fst r)
     . AssocMap.toList

{-# INLINABLE fromMapSafe #-}
fromMapSafe :: (Tx.Ord k) => AssocMap.Map k v -> SortedMap k v
fromMapSafe = sort

{-# INLINABLE fromMapUnsafe #-}
fromMapUnsafe :: AssocMap.Map k v -> SortedMap k v
fromMapUnsafe = SortedMap

{-# INLINABLE toMap #-}
toMap :: SortedMap k v -> AssocMap.Map k v
toMap = unSortedMap

{-# INLINABLE toList #-}
toList :: SortedMap k v -> [(k,v)]
toList = AssocMap.toList . unSortedMap

{-# INLINABLE fromListSafe #-}
fromListSafe :: (Tx.Ord k) => [(k,v)] -> SortedMap k v
fromListSafe = sort . AssocMap.fromListSafe

{-# INLINABLE fromListUnsafe #-}
fromListUnsafe :: [(k,v)] -> SortedMap k v
fromListUnsafe = fromMapUnsafe . AssocMap.fromList

{-# INLINABLE empty #-}
-- | An empty 'SortedMap'.
empty :: SortedMap k v
empty = SortedMap AssocMap.empty

{-# INLINABLE delete #-}
-- OPTIMIZE: Using AssocMap.delete works, but a version that stops earlier would be better
delete :: (Eq k) => k -> SortedMap k v -> SortedMap k v
delete k = fromMapUnsafe . AssocMap.delete k . toMap

{-# INLINABLE lookup #-}
-- OPTIMIZE: a manual implementation can stop earlier than AssocMap.lookup, upon missing keys only
lookup :: (Eq k) => k -> SortedMap k v -> Haskell.Maybe v
lookup k = AssocMap.lookup k . toMap

{-# INLINABLE minViewWithKey #-}
-- | Assumes that the SortedMap is valid.
minViewWithKey :: SortedMap k v -> Haskell.Maybe ((k,v), SortedMap k v)
minViewWithKey = fmap (\(f,s) -> (f, fromListUnsafe s)) . Tx.uncons . toList

{-# INLINABLE insert #-}
insert :: (Tx.Ord k) => k -> v -> SortedMap k v -> SortedMap k v
insert k v = SortedMap . AssocMap.fromList . insertInternal (k,v) . AssocMap.toList . unSortedMap

{-# INLINABLE insertInternal #-}
insertInternal :: (Tx.Ord k) => (k,v) -> [(k,v)] -> [(k,v)]
insertInternal (k,v) = go
    where
      go = \case
        [] -> [(k,v)]
        ((k',v'):ms) -> case k `compare` k' of
            EQ -> (k,v) : ms
            LT -> (k,v) : (k',v') : ms
            GT -> (k',v') : go ms

{-# INLINABLE isSorted #-}
isSorted :: (Tx.Ord k) => AssocMap.Map k v -> Bool
isSorted = go . AssocMap.toList
    where
      go ((xk,_):(yk,yv):rest) = xk < yk && go ((yk,yv):rest)
      go _                     = True

{-# INLINABLE isValid #-}
isValid :: (Tx.Ord k) => SortedMap k v -> Bool
isValid = isSorted . unSortedMap

Tx.makeLift ''SortedMap
