{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-| This is like `PlutusTx.AssocMap` but with the extra invariant that the entries are kept
sorted on the KEYS upon construction, insertion, and deletion.
As with "PlutusTx.AssocMap", using the unsafe API may lead to duplicate entries, whereas using the
safe one will not.
-}
module PlutusTx.SortedMap
    ( SortedMap
    , empty
    , insert
    , delete
    , lookup
    , member
    , null
    , minViewWithKey
    , isSortedDeDuped
    , isValid
    -- * conversion from/to AssocMap
    , insertionSortDeDup
    , mergeSort
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
import PlutusTx.Builtins as Tx (error)
import PlutusTx.Eq as Tx
import PlutusTx.Functor as Tx
import PlutusTx.IsData as Tx
import PlutusTx.Lift as Tx
import PlutusTx.List qualified as Tx
import PlutusTx.Maybe as Tx
import PlutusTx.Ord as Tx

import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax as TH
import Prelude qualified as Haskell

newtype SortedMap k v = SortedMap { unSortedMap :: AssocMap.Map k v }
  deriving stock (Generic, Haskell.Eq, Haskell.Show, TH.Lift)
  deriving newtype (Tx.Eq, Tx.Ord)

{- Uses the exact same underlying encoding as AssocMap.
In the encoding, we do not check that the SortedMap is valid;
we only check for sortedness at the decoding i.e. (Unsafe)FromData.
-}
deriving newtype instance (Tx.ToData k, Tx.ToData v) => Tx.ToData (SortedMap k v)

instance (Ord k, Tx.FromData k, Tx.FromData v) => Tx.FromData (SortedMap k v) where
    fromBuiltinData d = do
        assocMap <- fromBuiltinData d
        -- In the decoding, we check that the AssocMap is sorted
        -- OPTIMIZE: fuse isSorted check inside the inlined AssocMap.fromBuiltinData
        fromMapSafe assocMap

instance (Ord k, Tx.UnsafeFromData k, Tx.UnsafeFromData v) =>
         Tx.UnsafeFromData (SortedMap k v) where
    unsafeFromBuiltinData d =
        -- OPTIMIZE: fuse isSorted check inside the inlined AssocMap.unsafeFromBuiltinData
        let assocMap = unsafeFromBuiltinData d
        -- In the decoding, we check that the AssocMap is sorted&deduped
        in if isSortedDeDuped assocMap
           then SortedMap assocMap
           else Tx.error ()

{-# INLINABLE insertionSortDeDup #-}
-- | An insertion-sort that sorts and dedups.
-- Similar to 'AssocMap.fromListSafe' and 'AssocMap.insert', the function will dedup
-- by only keeping a single entry that precedes.
insertionSortDeDup :: (Tx.Ord k) => AssocMap.Map k v -> SortedMap k v
insertionSortDeDup = SortedMap . AssocMap.fromList . Tx.foldr insertInternal [] . AssocMap.toList

{-# INLINABLE mergeSort #-}
-- A stable merge-sort that retains duplicate entries.
-- NOTE: if the input AssocMap contains duplicates (invalid), the output
-- SortedMap will also contain duplicates and thus also be invalid.
mergeSort :: (Tx.Ord k) => AssocMap.Map k v -> SortedMap k v
mergeSort = SortedMap
     . AssocMap.fromList
     . Tx.sortBy (\ l r -> fst l `compare` fst r)
     . AssocMap.toList

{-# INLINABLE fromMapSafe #-}
fromMapSafe :: (Tx.Ord k) => AssocMap.Map k v -> Maybe (SortedMap k v)
fromMapSafe amap = if isSortedDeDuped amap
                   then Just $ SortedMap amap
                   else Nothing

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
-- | Will produce a valid (de-duplicated & sorted) SortedMap.
fromListSafe :: (Tx.Ord k) => [(k,v)] -> SortedMap k v
fromListSafe = insertionSortDeDup . AssocMap.fromListSafe

{-# INLINABLE fromListUnsafe #-}
fromListUnsafe :: [(k,v)] -> SortedMap k v
fromListUnsafe = fromMapUnsafe . AssocMap.fromList

{-# INLINABLE empty #-}
-- | An empty 'SortedMap'.
empty :: SortedMap k v
empty = SortedMap AssocMap.empty

{-# INLINABLE delete #-}
delete :: forall k v. (Ord k) => k -> SortedMap k v -> SortedMap k v
delete c (toList -> alist) = fromListUnsafe (go alist)
  where
    go [] = []
    go ms@(hd@(c', _) : rest) = case c `compare` c' of
                              LT -> ms
                              EQ -> rest
                              GT -> hd : go rest

{-# INLINABLE member #-}
-- | Is the key a member of the map?
member :: forall k v. (Ord k) => k -> SortedMap k v -> Bool
member k m = isJust (lookup k m)

-- | Is the map empty?
null :: SortedMap k v -> Bool
null = Tx.null . toList

{-# INLINABLE lookup #-}
-- | Find an entry in a 'SortedMap'.
lookup :: forall k v. (Tx.Ord k) => k -> SortedMap k v -> Haskell.Maybe v
lookup c (toList -> alist) =
  let
    go :: [(k, v)] -> Maybe v
    go []              = Nothing
    go ((c', i) : xs') = case c `compare` c' of
        LT -> Nothing
        EQ -> Just i
        GT -> go xs'
   in
    go alist

{-# INLINABLE minViewWithKey #-}
-- | Assumes that the SortedMap is valid.
minViewWithKey :: SortedMap k v -> Haskell.Maybe ((k,v), SortedMap k v)
minViewWithKey = fmap (\(f,s) -> (f, fromListUnsafe s)) . Tx.uncons . toList

{-# INLINABLE insert #-}
-- | Similar to 'AssocMap.insert', if a key already exists in the map, its entry
-- will be replaced with the new value.
insert :: (Tx.Ord k) => k -> v -> SortedMap k v -> SortedMap k v
insert k v = SortedMap . AssocMap.fromList . insertInternal (k,v) . AssocMap.toList . unSortedMap

{-# INLINABLE insertInternal #-}
-- | Internal-only: Operates directly on alists
insertInternal :: (Tx.Ord k) => (k,v) -> [(k,v)] -> [(k,v)]
insertInternal (k,v) = go
    where
      go = \case
        [] -> [(k,v)]
        ms@((k',v'):ms') -> case k `compare` k' of
            LT -> (k,v) : ms
            EQ -> (k,v) : ms'
            GT -> (k',v') : go ms'

{-# INLINABLE isSortedDeDuped #-}
-- | Note that it also checks for duplicates
isSortedDeDuped :: (Tx.Ord k) => AssocMap.Map k v -> Bool
isSortedDeDuped (AssocMap.toList -> alist) =
    case alist of
        []            -> True
        (xk,_) : rest -> go xk rest
  where
    go xk ((yk,_) : rest) =
        -- we use if-then-else instead of (&&) because (&&) might not short-circuit
        -- See Note [Short-circuit evaluation for && and ||]
        if xk < yk
        then go yk rest
        else False
    go _ _ = True

{-# INLINABLE isValid #-}
isValid :: (Tx.Ord k) => SortedMap k v -> Bool
isValid = isSortedDeDuped . unSortedMap

Tx.makeLift ''SortedMap
