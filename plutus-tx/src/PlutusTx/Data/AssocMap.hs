{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}

module PlutusTx.Data.AssocMap (
  Map,
  lookup,
  member,
  insert,
  delete,
  singleton,
  empty,
  null,
  toList,
  toBuiltinList,
  safeFromList,
  unsafeFromList,
  unsafeFromBuiltinList,
  noDuplicateKeys,
  all,
  any,
  union,
  unionWith,
  keys,
  map,
  mapThese,
  foldr,
  ) where

import PlutusTx.Builtins qualified as P
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.IsData qualified as P
import PlutusTx.Lift (makeLift)
import PlutusTx.List qualified as List
import PlutusTx.Prelude hiding (all, any, foldr, map, null, toList, uncons)
import PlutusTx.Prelude qualified
import PlutusTx.These


import Prelude qualified as Haskell

{- | A map associating keys and values backed by `P.BuiltinData`.

This implementation has the following characteristics:

  * The `P.toBuiltinData` and `P.unsafeFromBuiltinData` operations are no-op.
  * Other operations are slower than @PlutusTx.AssocMap.Map@, although equality
    checks on keys can be faster due to `P.equalsData`.
  * Many operations involve converting the keys and\/or values to\/from `P.BuiltinData`.

Therefore this implementation is likely a better choice than "PlutusTx.AssocMap.Map"
if it is part of a data type defined using @asData@, and the key and value types
have efficient `P.toBuiltinData` and `P.unsafeFromBuiltinData` operations (e.g., they
are primitive types or types defined using @asData@).

A `Map` is considered well-defined if it has no duplicate keys. Most operations
preserve the definedness of the resulting `Map` unless otherwise noted.
It is important to observe that, in comparison to standard map implementations,
this implementation provides slow lookup and update operations because it is based
on a list representation.
-}
newtype Map k a = Map (BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData))
  deriving stock (Haskell.Show)

instance P.ToData (Map k a) where
  {-# INLINEABLE toBuiltinData #-}
  toBuiltinData (Map d) = BI.mkMap d

instance P.FromData (Map k a) where
  {-# INLINABLE fromBuiltinData #-}
  fromBuiltinData = Just . Map . BI.unsafeDataAsMap

instance P.UnsafeFromData (Map k a) where
  {-# INLINABLE unsafeFromBuiltinData #-}
  unsafeFromBuiltinData = Map . BI.unsafeDataAsMap

{-# INLINEABLE lookup #-}
-- | Look up the value corresponding to the key.
-- If the `Map` is not well-defined, the result is the value associated with
-- the left-most occurrence of the key in the list.
-- This operation is O(n).
lookup :: forall k a. (P.ToData k, P.UnsafeFromData a) => k -> Map k a -> Maybe a
lookup (P.toBuiltinData -> k) (Map m) = P.unsafeFromBuiltinData <$> lookup' k m

lookup'
  :: BuiltinData
  -> BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
  -> Maybe BuiltinData
lookup' k m = go m
  where
    go xs =
      P.matchList
        xs
        (\() -> Nothing)
        ( \hd ->
            let k' = BI.fst hd
             in if P.equalsData k k'
                  then \_ -> Just (BI.snd hd)
                  else go
        )

{-# INLINEABLE member #-}
-- | Check if the key is in the `Map`.
member :: forall k a. (P.ToData k) => k -> Map k a -> Bool
member (P.toBuiltinData -> k) (Map m) = member' k m

member' :: BuiltinData -> BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> Bool
member' k = go
  where
    go :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> Bool
    go xs =
      P.matchList
        xs
        (\() -> False)
        ( \hd ->
            let k' = BI.fst hd
             in if P.equalsData k k'
                  then \_ -> True
                  else go
        )

{-# INLINEABLE insert #-}
-- | Insert a key-value pair into the `Map`. If the key is already present,
-- the value is updated.
insert :: forall k a. (P.ToData k, P.ToData a) => k -> a -> Map k a -> Map k a
insert (P.toBuiltinData -> k) (P.toBuiltinData -> a) (Map m) = Map $ insert' k a m

insert'
  :: BuiltinData
  -> BuiltinData
  -> BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
  -> BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
insert' k a = go
  where
    go ::
      BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) ->
      BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
    go xs =
      P.matchList
        xs
        (\() -> BI.mkCons (BI.mkPairData k a) nil)
        ( \hd tl ->
            let k' = BI.fst hd
             in if P.equalsData k k'
                  then BI.mkCons (BI.mkPairData k a) tl
                  else BI.mkCons hd (go tl)
        )

{-# INLINEABLE delete #-}
-- | Delete a key value pair from the `Map`.
-- If the `Map` is not well-defined, it deletes the pair associated with the
-- left-most occurrence of the key in the list.
delete :: forall k a. (P.ToData k) => k -> Map k a -> Map k a
delete (P.toBuiltinData -> k) (Map m) = Map $ delete' k m

delete' ::
  BuiltinData ->
  BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) ->
  BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
delete' k = go
  where
    go ::
      BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) ->
      BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
    go xs =
      P.matchList
        xs
        (\() -> nil)
        ( \hd tl ->
            let k' = BI.fst hd
             in if P.equalsData k k'
                  then tl
                  else BI.mkCons hd (go tl)
        )

{-# INLINEABLE singleton #-}
-- | Create an `Map` with a single key-value pair.
singleton :: forall k a. (P.ToData k, P.ToData a) => k -> a -> Map k a
singleton (P.toBuiltinData -> k) (P.toBuiltinData -> a) =
  Map $ BI.mkCons (BI.mkPairData k a) nil

{-# INLINEABLE empty #-}
-- | An empty `Map`.
empty :: forall k a. Map k a
empty = Map nil

{-# INLINEABLE null #-}
-- | Check if the `Map` is empty.
null :: forall k a. Map k a -> Bool
null (Map m) = P.null m

{-# INLINEABLE safeFromList #-}
-- | Create an `Map` from a list of key-value pairs.
-- In case of duplicates, this function will keep only one entry (the one that precedes).
-- In other words, this function de-duplicates the input list.
safeFromList :: forall k a . (P.ToData k, P.ToData a) => [(k, a)] -> Map k a
safeFromList =
  Map
    . toOpaque
    . List.foldr (uncurry go) []
  where
    go k v [] = [(P.toBuiltinData k, P.toBuiltinData v)]
    go k v ((k', v') : rest) =
      if P.toBuiltinData k == k'
        then (P.toBuiltinData k, P.toBuiltinData v) : go k v rest
        else (P.toBuiltinData k', P.toBuiltinData v') : go k v rest

{-# INLINEABLE unsafeFromList #-}
-- | Unsafely create an 'Map' from a list of pairs.
-- This should _only_ be applied to lists which have been checked to not
-- contain duplicate keys, otherwise the resulting 'Map' will contain
-- conflicting entries (two entries sharing the same key), and therefore be ill-defined.
unsafeFromList :: (P.ToData k, P.ToData a) => [(k, a)] -> Map k a
unsafeFromList =
  Map
    . toOpaque
    . PlutusTx.Prelude.map (\(k, a) -> (P.toBuiltinData k, P.toBuiltinData a))

{-# INLINEABLE noDuplicateKeys #-}
-- | Check if the `Map` is well-defined. Warning: this operation is O(n^2).
noDuplicateKeys :: forall k a. Map k a -> Bool
noDuplicateKeys (Map m) = go m
  where
    go :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> Bool
    go xs =
      P.matchList
        xs
        (\() -> True)
        ( \hd tl ->
            let k = BI.fst hd
             in if member k (Map tl) then False else go tl
        )

{-# INLINEABLE all #-}
--- | Check if all values in the `Map` satisfy the predicate.
all :: forall k a. (P.UnsafeFromData a) => (a -> Bool) -> Map k a -> Bool
all p (Map m) = go m
  where
    go :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> Bool
    go xs =
      P.matchList
        xs
        (\() -> True)
        ( \hd ->
            let a = P.unsafeFromBuiltinData (BI.snd hd)
             in if p a then go else \_ -> False
        )

{-# INLINEABLE any #-}
-- | Check if any value in the `Map` satisfies the predicate.
any :: forall k a. (P.UnsafeFromData a) => (a -> Bool) -> Map k a -> Bool
any p (Map m) = go m
  where
    go :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> Bool
    go xs =
      P.matchList
        xs
        (\() -> False)
        ( \hd ->
            let a = P.unsafeFromBuiltinData (BI.snd hd)
             in if p a then \_ -> True else go
        )

{-# INLINEABLE union #-}

-- | Combine two 'Map's into one. It saves both values if the key is present in both maps.
union ::
  forall k a b.
  (P.UnsafeFromData a, P.UnsafeFromData b, P.ToData a, P.ToData b) =>
  Map k a ->
  Map k b ->
  Map k (These a b)
union (Map ls) (Map rs) = Map res
  where
    goLeft xs =
      P.matchList
        xs
        (\() -> nil)
        ( \hd tl ->
            let k = BI.fst hd
                v = BI.snd hd
                v' = case lookup' k rs of
                  Just r ->
                    P.toBuiltinData
                      ( These
                          (P.unsafeFromBuiltinData v)
                          (P.unsafeFromBuiltinData r)
                        :: These a b
                      )
                  Nothing ->
                    P.toBuiltinData (This (P.unsafeFromBuiltinData v) :: These a b)
             in BI.mkCons (BI.mkPairData k v') (goLeft tl)
        )

    goRight xs =
      P.matchList
        xs
        (\() -> nil)
        ( \hd tl ->
            let k = BI.fst hd
                v = BI.snd hd
                v' = case lookup' k ls of
                  Just r ->
                    P.toBuiltinData
                      ( These
                          (P.unsafeFromBuiltinData v)
                          (P.unsafeFromBuiltinData r)
                        :: These a b
                      )
                  Nothing ->
                    P.toBuiltinData (That (P.unsafeFromBuiltinData v) :: These a b)
             in BI.mkCons (BI.mkPairData k v') (goRight tl)
        )

    res = goLeft ls `safeAppend` goRight rs

    safeAppend xs1 xs2 =
      P.matchList
        xs1
        (\() -> xs2)
        ( \hd tl ->
            let k = BI.fst hd
                v = BI.snd hd
             in insert' k v (safeAppend tl xs2)
        )

{-# INLINEABLE unionWith #-}
-- | Combine two 'Map's with the given combination function.
unionWith ::
  forall k a.
  (P.UnsafeFromData a, P.ToData a) =>
  (a -> a -> a) ->
  Map k a ->
  Map k a ->
  Map k a
unionWith f (Map ls) (Map rs) =
  Map res
  where
    ls' :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
    ls' = go ls
      where
        go xs =
          P.matchList
            xs
            (\() -> nil)
            ( \hd tl ->
                let k' = BI.fst hd
                    v' = BI.snd hd
                    v'' = case lookup' k' rs of
                      Just r ->
                        P.toBuiltinData
                          (f (P.unsafeFromBuiltinData v') (P.unsafeFromBuiltinData r))
                      Nothing -> v'
                 in BI.mkCons (BI.mkPairData k' v'') (go tl)
            )

    rs' :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
    rs' = go rs
      where
        go xs =
          P.matchList
            xs
            (\() -> nil)
            ( \hd tl ->
                let k' = BI.fst hd
                    tl' = go tl
                 in if member' k' ls
                      then tl'
                      else BI.mkCons hd tl'
            )

    res :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
    res = go rs' ls'
      where
        go acc xs =
          P.matchList
            xs
            (\() -> acc)
            (\hd -> go (BI.mkCons hd acc))

{-# INLINEABLE toList #-}
-- | Convert the `Map` to a list of key-value pairs. This operation is O(n).
-- See 'toBuiltinList' for a more efficient alternative.
toList :: (P.UnsafeFromData k, P.UnsafeFromData a) => Map k a -> [(k, a)]
toList d = go (toBuiltinList d)
  where
    go xs =
      P.matchList
        xs
        (\() -> [])
        ( \hd tl ->
            (P.unsafeFromBuiltinData (BI.fst hd), P.unsafeFromBuiltinData (BI.snd hd))
              : go tl
        )

{-# INLINEABLE toBuiltinList #-}
-- | Convert the `Map` to a `P.BuiltinList` of key-value pairs. This operation is O(1).
toBuiltinList :: Map k a -> BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
toBuiltinList (Map d) = d

{-# INLINEABLE unsafeFromBuiltinList #-}
-- | Unsafely create an 'Map' from a `P.BuiltinList` of key-value pairs.
-- This function is unsafe because it assumes that the elements of the list can be safely
-- decoded from their 'BuiltinData' representation.
unsafeFromBuiltinList ::
  forall k a.
  BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) ->
  Map k a
unsafeFromBuiltinList = Map

{-# INLINEABLE nil #-}
-- | An empty `P.BuiltinList` of key-value pairs.
nil :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
nil = BI.mkNilPairData BI.unitval

keys'
  :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
  -> BI.BuiltinList BuiltinData
keys' = go
  where
    go xs =
      P.matchList
        xs
        (\() -> BI.mkNilData BI.unitval)
        ( \hd tl ->
            let k = BI.fst hd
             in BI.mkCons k (go tl)
        )

{-# INLINEABLE keys #-}
keys :: forall k a. Map k a -> BI.BuiltinList BuiltinData
keys (Map m) = keys' m

{-# INLINEABLE mapThese #-}
mapThese
  :: forall v k a b
  . ( P.ToData a, P.ToData b, P.UnsafeFromData v)
  => (v -> These a b) -> Map k v -> (Map k a, Map k b)
mapThese f (Map m) = (Map ls, Map rs)
  where
    (ls, rs) = go m
    go
      :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
      ->
        ( BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
        , BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
        )
    go xs =
      P.matchList
        xs
        (\() -> (nil, nil))
        ( \hd tl ->
            let k = BI.fst hd
                v = BI.snd hd
                (ls', rs') = go tl
             in case f' v of
                  This l' -> (BI.mkCons (BI.mkPairData k (P.toBuiltinData l')) ls', rs')
                  That r' -> (ls', BI.mkCons (BI.mkPairData k (P.toBuiltinData r')) rs')
                  These l' r' ->
                    ( BI.mkCons (BI.mkPairData k (P.toBuiltinData l')) ls'
                    , BI.mkCons (BI.mkPairData k (P.toBuiltinData r')) rs'
                    )
        )
    f' :: BuiltinData -> These a b
    f' = f . P.unsafeFromBuiltinData

{-# INLINEABLE map #-}
map :: forall k a b. (P.UnsafeFromData a, P.ToData b) => (a -> b) -> Map k a -> Map k b
map f (Map m) = Map $ go m
  where
    go xs =
      P.matchList
        xs
        (\() -> nil)
        ( \hd tl ->
            let k = BI.fst hd
                v = BI.snd hd
             in
              BI.mkCons
                (BI.mkPairData k (P.toBuiltinData (f (P.unsafeFromBuiltinData v))))
                (go tl)
        )

{-# INLINEABLE foldr #-}
foldr :: forall a b k. (P.UnsafeFromData a) => (a -> b -> b) -> b -> Map k a -> b
foldr f z (Map m) = go m
  where
    go xs =
      P.matchList
        xs
        (\() -> z)
        ( \hd tl ->
            let v = BI.snd hd
             in f (P.unsafeFromBuiltinData v) (go tl)
        )

makeLift ''Map
