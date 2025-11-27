{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}

module PlutusTx.Data.AssocMap
  ( Map
  , lookup
  , member
  , insert
  , delete
  , singleton
  , empty
  , null
  , toSOPList
  , toBuiltinList
  , safeFromSOPList
  , unsafeFromSOPList
  , unsafeFromDataList
  , unsafeFromBuiltinList
  , noDuplicateKeys
  , all
  , any
  , union
  , unionWith
  , keys
  , elems
  , map
  , mapThese
  , foldr
  , filter
  , mapWithKey
  , mapMaybe
  , mapMaybeWithKey
  ) where

import Data.Coerce (coerce)
import PlutusTx.Builtins qualified as P
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Data.List (List)
import PlutusTx.Data.List qualified as Data.List
import PlutusTx.IsData qualified as P
import PlutusTx.Lift (makeLift)
import PlutusTx.List qualified as SOP.List
import PlutusTx.Prelude hiding (mapMaybe)
import PlutusTx.These
import Prettyprinter (Pretty (..))

import Prelude qualified as Haskell

{-| A map associating keys and values backed by `P.BuiltinData`.

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
on a list representation. -}
newtype Map k a = Map (BuiltinList (BuiltinPair BuiltinData BuiltinData))
  deriving stock (Haskell.Show)

instance P.ToData (Map k a) where
  {-# INLINEABLE toBuiltinData #-}
  toBuiltinData (Map d) = BI.mkMap d
instance P.FromData (Map k a) where
  {-# INLINEABLE fromBuiltinData #-}
  fromBuiltinData = Just . Map . BI.unsafeDataAsMap

instance P.UnsafeFromData (Map k a) where
  {-# INLINEABLE unsafeFromBuiltinData #-}
  unsafeFromBuiltinData = Map . BI.unsafeDataAsMap

instance
  ( Pretty k
  , Pretty a
  , P.UnsafeFromData k
  , P.UnsafeFromData a
  )
  => Pretty (Map k a)
  where
  pretty = pretty . toSOPList

{-| Look up the value corresponding to the key.
If the `Map` is not well-defined, the result is the value associated with
the left-most occurrence of the key in the list.
This operation is O(n). -}
lookup :: forall k a. (P.ToData k, P.UnsafeFromData a) => k -> Map k a -> Maybe a
lookup (P.toBuiltinData -> k) (Map m) = P.unsafeFromBuiltinData <$> lookup' k m
{-# INLINEABLE lookup #-}

lookup'
  :: BuiltinData
  -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
  -> Maybe BuiltinData
lookup' k m = go m
  where
    go =
      P.caseList'
        Nothing
        ( \hd ->
            let k' = BI.fst hd
             in if P.equalsData k k'
                  then \_ -> Just (BI.snd hd)
                  else go
        )

-- | Check if the key is in the `Map`.
member :: forall k a. P.ToData k => k -> Map k a -> Bool
member (P.toBuiltinData -> k) (Map m) = member' k m
{-# INLINEABLE member #-}

member' :: BuiltinData -> BuiltinList (BuiltinPair BuiltinData BuiltinData) -> Bool
member' k = go
  where
    go :: BuiltinList (BuiltinPair BuiltinData BuiltinData) -> Bool
    go =
      P.caseList'
        False
        ( \hd ->
            let k' = BI.fst hd
             in if P.equalsData k k'
                  then \_ -> True
                  else go
        )

{-| Insert a key-value pair into the `Map`. If the key is already present,
the value is updated. -}
insert :: forall k a. (P.ToData k, P.ToData a) => k -> a -> Map k a -> Map k a
insert (P.toBuiltinData -> k) (P.toBuiltinData -> a) (Map m) = Map $ insert' k a m
{-# INLINEABLE insert #-}

insert'
  :: BuiltinData
  -> BuiltinData
  -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
  -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
insert' k a = go
  where
    nilCase = BI.mkCons (BI.mkPairData k a) nil
    go
      :: BuiltinList (BuiltinPair BuiltinData BuiltinData)
      -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
    go =
      P.caseList'
        nilCase
        ( \hd ->
            if P.equalsData k (BI.fst hd)
              then BI.mkCons (BI.mkPairData k a)
              else BI.mkCons hd . go
        )

{-| Delete a key value pair from the `Map`.
If the `Map` is not well-defined, it deletes the pair associated with the
left-most occurrence of the key in the list. -}
delete :: forall k a. P.ToData k => k -> Map k a -> Map k a
delete (P.toBuiltinData -> k) = coerce $ delete' k
{-# INLINEABLE delete #-}

delete'
  :: BuiltinData
  -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
  -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
delete' k = go
  where
    go
      :: BuiltinList (BuiltinPair BuiltinData BuiltinData)
      -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
    go =
      P.caseList'
        nil
        ( \hd ->
            if P.equalsData k (BI.fst hd)
              then id
              else BI.mkCons hd . go
        )

-- | Create an `Map` with a single key-value pair.
singleton :: forall k a. (P.ToData k, P.ToData a) => k -> a -> Map k a
singleton (P.toBuiltinData -> k) (P.toBuiltinData -> a) =
  coerce $ BI.mkCons (BI.mkPairData k a) nil
{-# INLINEABLE singleton #-}

-- | An empty `Map`.
empty :: forall k a. Map k a
empty = coerce nil
{-# INLINEABLE empty #-}

-- | Check if the `Map` is empty.
null :: forall k a. Map k a -> Bool
null =
  coerce
    @(BuiltinList (BuiltinPair BuiltinData BuiltinData) -> Bool)
    P.null
{-# INLINEABLE null #-}

{-| Create an `Map` from a sums of products list of key-value pairs.
In case of duplicates, this function will keep only one entry (the one that precedes).
In other words, this function de-duplicates the input list.
Warning: this function is very slow. If you know that the input list does not contain
duplicate keys, use one of the unsafe functions instead. -}
safeFromSOPList :: forall k a. (P.ToData k, P.ToData a) => [(k, a)] -> Map k a
safeFromSOPList =
  Map
    . toOpaque
    . SOP.List.foldr (uncurry go) []
  where
    go :: k -> a -> [(BuiltinData, BuiltinData)] -> [(BuiltinData, BuiltinData)]
    go k v [] = [(P.toBuiltinData k, P.toBuiltinData v)]
    go k v ((k', v') : rest) =
      if P.toBuiltinData k == k'
        then (P.toBuiltinData k, P.toBuiltinData v) : go k v rest
        else (k', v') : go k v rest
{-# INLINEABLE safeFromSOPList #-}

{-| Unsafely create an 'Map' from a sums of products list of pairs.
This should _only_ be applied to lists which have been checked to not
contain duplicate keys, otherwise the resulting 'Map' will contain
conflicting entries (two entries sharing the same key), and therefore be ill-defined.
Warning: this requires traversing the list and encoding the keys and values, so it
should be avoided in favor of 'unsafeFromBuiltinList' if the input is already in
'BuiltinData' form. -}
unsafeFromSOPList :: (P.ToData k, P.ToData a) => [(k, a)] -> Map k a
unsafeFromSOPList =
  Map
    . toOpaque
    . SOP.List.map (\(k, a) -> (P.toBuiltinData k, P.toBuiltinData a))
{-# INLINEABLE unsafeFromSOPList #-}

{-| Unsafely create an 'Map' from a `P.BuiltinList` of key-value pairs. This operation
is O(1).
This function is unsafe because it assumes that the elements of the list can be safely
decoded from their 'BuiltinData' representation. It also does not deduplicate the keys. -}
unsafeFromBuiltinList
  :: forall k a
   . BuiltinList (BuiltinPair BuiltinData BuiltinData)
  -> Map k a
unsafeFromBuiltinList = coerce
{-# INLINEABLE unsafeFromBuiltinList #-}

{-| Unsafely create an 'Map' from a `List` of key-value pairs.
This function is unsafe because it assumes that the elements of the list can be safely
decoded from their 'BuiltinData' representation. It also does not deduplicate the keys. -}
unsafeFromDataList :: List (a, k) -> Map k a
unsafeFromDataList =
  coerce . go . Data.List.toBuiltinList
  where
    go
      :: BuiltinList BuiltinData
      -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
    go =
      P.caseList'
        nil
        ( \hd tl ->
            let (a, b) = P.unsafeFromBuiltinData hd
             in BI.mkCons (BI.mkPairData a b) (go tl)
        )
{-# INLINEABLE unsafeFromDataList #-}

{-| Convert the `Map` to a list of key-value pairs. This operation is O(n).
See 'toBuiltinList' for a more efficient alternative. -}
toSOPList :: (P.UnsafeFromData k, P.UnsafeFromData a) => Map k a -> [(k, a)]
toSOPList d = go (toBuiltinList d)
  where
    go =
      P.caseList'
        []
        ( \hd tl ->
            (P.unsafeFromBuiltinData (BI.fst hd), P.unsafeFromBuiltinData (BI.snd hd))
              : go tl
        )
{-# INLINEABLE toSOPList #-}

-- | Convert the `Map` to a `P.BuiltinList` of key-value pairs. This operation is O(1).
toBuiltinList :: Map k a -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
toBuiltinList = coerce
{-# INLINEABLE toBuiltinList #-}

-- | Check if the `Map` is well-defined. Warning: this operation is O(n^2).
noDuplicateKeys :: forall k a. Map k a -> Bool
noDuplicateKeys (Map m) = go m
  where
    go :: BuiltinList (BuiltinPair BuiltinData BuiltinData) -> Bool
    go =
      P.caseList'
        True
        ( \hd tl ->
            if member' (BI.fst hd) tl then False else go tl
        )
{-# INLINEABLE noDuplicateKeys #-}

--- | Check if all values in the `Map` satisfy the predicate.
all :: forall k a. P.UnsafeFromData a => (a -> Bool) -> Map k a -> Bool
all p = coerce go
  where
    go :: BuiltinList (BuiltinPair BuiltinData BuiltinData) -> Bool
    go =
      P.caseList'
        True
        ( \hd ->
            if p (P.unsafeFromBuiltinData (BI.snd hd))
              then go
              else \_ -> False
        )
{-# INLINEABLE all #-}

-- | Check if any value in the `Map` satisfies the predicate.
any :: forall k a. P.UnsafeFromData a => (a -> Bool) -> Map k a -> Bool
any p = coerce go
  where
    go :: BuiltinList (BuiltinPair BuiltinData BuiltinData) -> Bool
    go =
      P.caseList'
        False
        ( \hd ->
            if p (P.unsafeFromBuiltinData (BI.snd hd))
              then \_ -> True
              else go
        )
{-# INLINEABLE any #-}

-- | Combine two 'Map's into one. It saves both values if the key is present in both maps.
union
  :: forall k a b
   . (P.UnsafeFromData a, P.UnsafeFromData b, P.ToData a, P.ToData b)
  => Map k a
  -> Map k b
  -> Map k (These a b)
union (Map ls) (Map rs) = Map res
  where
    goLeft =
      P.caseList'
        nil
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

    goRight =
      P.caseList'
        nil
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
      P.matchList'
        xs1
        xs2
        ( \hd tl ->
            let k = BI.fst hd
                v = BI.snd hd
             in insert' k v (safeAppend tl xs2)
        )
{-# INLINEABLE union #-}

-- | Combine two 'Map's with the given combination function.
unionWith
  :: forall k a
   . (P.UnsafeFromData a, P.ToData a)
  => (a -> a -> a)
  -> Map k a
  -> Map k a
  -> Map k a
unionWith f (Map ls) (Map rs) =
  Map res
  where
    ls' :: BuiltinList (BuiltinPair BuiltinData BuiltinData)
    ls' = go ls
      where
        go =
          P.caseList'
            nil
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

    rs' :: BuiltinList (BuiltinPair BuiltinData BuiltinData)
    rs' = go rs
      where
        go =
          P.caseList'
            nil
            ( \hd tl ->
                let k' = BI.fst hd
                    tl' = go tl
                 in if member' k' ls
                      then tl'
                      else BI.mkCons hd tl'
            )

    res :: BuiltinList (BuiltinPair BuiltinData BuiltinData)
    res = go rs' ls'
      where
        go acc =
          P.caseList'
            acc
            (\hd -> go (BI.mkCons hd acc))
{-# INLINEABLE unionWith #-}

-- | An empty `P.BuiltinList` of key-value pairs.
nil :: BuiltinList (BuiltinPair BuiltinData BuiltinData)
nil = P.mkNil
{-# INLINEABLE nil #-}

keys'
  :: BuiltinList (BuiltinPair BuiltinData BuiltinData)
  -> BuiltinList BuiltinData
keys' = go
  where
    go =
      P.caseList'
        P.mkNil
        ( \hd ->
            BI.mkCons (BI.fst hd) . go
        )

keys :: forall k a. Map k a -> List k
keys = Data.List.fromBuiltinList . keys' . coerce
{-# INLINEABLE keys #-}

elems :: forall k a. Map k a -> List a
elems = Data.List.fromBuiltinList . go . coerce
  where
    go
      :: BuiltinList (BuiltinPair BuiltinData BuiltinData)
      -> BuiltinList BuiltinData
    go =
      P.caseList'
        P.mkNil
        ( \hd ->
            BI.mkCons (BI.snd hd) . go
        )
{-# INLINEABLE elems #-}

mapThese
  :: forall v k a b
   . (P.ToData a, P.ToData b, P.UnsafeFromData v)
  => (v -> These a b) -> Map k v -> (Map k a, Map k b)
mapThese f (Map m) = (Map ls, Map rs)
  where
    nilCase = (nil, nil)
    (ls, rs) = go m
    go
      :: BuiltinList (BuiltinPair BuiltinData BuiltinData)
      -> ( BuiltinList (BuiltinPair BuiltinData BuiltinData)
         , BuiltinList (BuiltinPair BuiltinData BuiltinData)
         )
    go =
      P.caseList'
        nilCase
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
{-# INLINEABLE mapThese #-}

map :: forall k a b. (P.UnsafeFromData a, P.ToData b) => (a -> b) -> Map k a -> Map k b
map f = coerce go
  where
    go =
      P.caseList'
        nil
        ( \hd ->
            let (k, v) = P.pairToPair hd
             in BI.mkCons
                  (BI.mkPairData k (P.toBuiltinData (f (P.unsafeFromBuiltinData v))))
                  . go
        )
{-# INLINEABLE map #-}

foldr
  :: forall a b k
   . P.UnsafeFromData a
  => (a -> b -> b) -> b -> Map k a -> b
foldr f z = coerce go
  where
    go :: BuiltinList (BuiltinPair BuiltinData BuiltinData) -> b
    go =
      P.caseList'
        z
        ( \hd ->
            f (P.unsafeFromBuiltinData (BI.snd hd)) . go
        )
{-# INLINEABLE foldr #-}

filter
  :: forall k a
   . P.UnsafeFromData a
  => (a -> Bool) -> Map k a -> Map k a
filter p = coerce go
  where
    go =
      P.caseList'
        nil
        ( \hd ->
            if p (P.unsafeFromBuiltinData (BI.snd hd))
              then BI.mkCons hd . go
              else go
        )
{-# INLINEABLE filter #-}

mapWithKey
  :: forall k a b
   . (P.UnsafeFromData k, P.UnsafeFromData a, P.ToData b)
  => (k -> a -> b) -> Map k a -> Map k b
mapWithKey f = coerce go
  where
    go =
      P.caseList'
        nil
        ( \hd ->
            let (k, v) = P.pairToPair hd
             in BI.mkCons
                  ( BI.mkPairData
                      k
                      ( P.toBuiltinData
                          ( f
                              (P.unsafeFromBuiltinData k)
                              (P.unsafeFromBuiltinData v)
                          )
                      )
                  )
                  . go
        )
{-# INLINEABLE mapWithKey #-}

mapMaybe
  :: forall k a b
   . (P.UnsafeFromData a, P.ToData b)
  => (a -> Maybe b) -> Map k a -> Map k b
mapMaybe f = coerce go
  where
    go =
      P.caseList'
        nil
        ( \hd ->
            let (k, v) = P.pairToPair hd
             in case f (P.unsafeFromBuiltinData v) of
                  Just v' ->
                    BI.mkCons
                      (BI.mkPairData k (P.toBuiltinData v'))
                      . go
                  Nothing -> go
        )
{-# INLINEABLE mapMaybe #-}

mapMaybeWithKey
  :: forall k a b
   . (P.UnsafeFromData k, P.UnsafeFromData a, P.ToData b)
  => (k -> a -> Maybe b) -> Map k a -> Map k b
mapMaybeWithKey f = coerce go
  where
    go =
      P.caseList'
        nil
        ( \hd ->
            let (k, v) = P.pairToPair hd
             in case f (P.unsafeFromBuiltinData k) (P.unsafeFromBuiltinData v) of
                  Just v' ->
                    BI.mkCons
                      (BI.mkPairData k (P.toBuiltinData v'))
                      . go
                  Nothing -> go
        )
{-# INLINEABLE mapMaybeWithKey #-}

makeLift ''Map
