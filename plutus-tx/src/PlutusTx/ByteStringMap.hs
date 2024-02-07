{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | A map represented as an "association list" of key-value pairs.
module PlutusTx.ByteStringMap (
  Map,
  K,
  singleton,
  empty,
  null,
  fromList,
  fromListSafe,
  toList,
  keys,
  elems,
  lookup,
  member,
  insert,
  delete,
  union,
  unionWith,
  filter,
  mapWithKey,
  mapMaybe,
  mapMaybeWithKey,
  all,
  mapThese,
) where

import Prelude qualified as Haskell

import PlutusTx.Builtins qualified as P
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.IsData
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude hiding (all, filter, mapMaybe, null, toList)
import PlutusTx.Prelude qualified as P
import PlutusTx.These

import Control.DeepSeq (NFData)
import Data.Data
import GHC.Generics (Generic)
import Prettyprinter (Pretty (..))

{- HLINT ignore "Use newtype instead of data" -}

type K = P.BuiltinByteString

-- | A 'Map' of key-value pairs.
newtype Map v = Map {unMap :: [(K, v)]}
  deriving stock (Generic, Haskell.Eq, Haskell.Show, Data)
  deriving newtype (Eq, Ord, NFData)

-- Hand-written instances to use the underlying 'Map' type in 'Data', and
-- to be reasonably efficient.
instance (ToData v) => ToData (Map v) where
  toBuiltinData (Map es) = BI.mkMap (mapToBuiltin es)
    where
      {-# INLINE mapToBuiltin #-}
      mapToBuiltin :: [(K, v)] -> BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData)
      mapToBuiltin = go
        where
          go :: [(K, v)] -> BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData)
          go []            = BI.mkNilPairData BI.unitval
          go ((k, v) : xs) = BI.mkCons (BI.mkPairData (toBuiltinData k) (toBuiltinData v)) (go xs)

instance (FromData v) => FromData (Map v) where
  fromBuiltinData d =
    P.matchData'
      d
      (\_ _ -> Nothing)
      (\es -> Map <$> traverseFromBuiltin es)
      (const Nothing)
      (const Nothing)
      (const Nothing)
    where
      {-# INLINE traverseFromBuiltin #-}
      traverseFromBuiltin ::
        BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData) ->
        Maybe [(K, v)]
      traverseFromBuiltin = go
        where
          go :: BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData) -> Maybe [(K, v)]
          go l =
            BI.chooseList
              l
              (const (pure []))
              ( \_ ->
                  let tup = BI.head l
                   in liftA2
                        (:)
                        (liftA2 (,) (fromBuiltinData $ BI.fst tup) (fromBuiltinData $ BI.snd tup))
                        (go (BI.tail l))
              )
              ()

instance (UnsafeFromData v) => UnsafeFromData (Map v) where
  -- The `~` here enables `BI.unsafeDataAsMap d` to be inlined, which reduces costs slightly.
  -- Without the `~`, the inliner would consider it not effect safe to inline.
  -- We can remove the `~` once we make the inliner smart enough to inline them.
  -- See https://github.com/IntersectMBO/plutus/pull/5371#discussion_r1297833685
  unsafeFromBuiltinData d = let ~es = BI.unsafeDataAsMap d in Map $ mapFromBuiltin es
    where
      {-# INLINE mapFromBuiltin #-}
      mapFromBuiltin :: BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData) -> [(K, v)]
      mapFromBuiltin = go
        where
          go :: BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData) -> [(K, v)]
          go l =
            BI.chooseList
              l
              (const [])
              ( \_ ->
                  let tup = BI.head l
                   in (unsafeFromBuiltinData $ BI.fst tup, unsafeFromBuiltinData $ BI.snd tup)
                        : go (BI.tail l)
              )
              ()

instance Functor Map where
  {-# INLINEABLE fmap #-}
  fmap f (Map mp) = Map (fmap (fmap f) mp)

instance Foldable Map where
  {-# INLINEABLE foldr #-}
  foldr f z (Map mp) = foldr (f . snd) z mp

instance Traversable Map where
  {-# INLINEABLE traverse #-}
  traverse f (Map mp) = Map <$> traverse (traverse f) mp

-- This is the "better" instance for Maps that various people
-- have suggested, which merges conflicting entries with
-- the underlying semigroup for values.
instance (Semigroup v) => Semigroup (Map v) where
  (<>) = unionWith (<>)

instance (Semigroup v) => Monoid (Map v) where
  mempty = empty

instance (Pretty v) => Pretty (Map v) where
  pretty (Map mp) = pretty mp

{-# INLINEABLE fromList #-}
fromList :: [(K, v)] -> Map v
fromList = Map

{-# INLINEABLE fromListSafe #-}
fromListSafe :: [(K, v)] -> Map v
fromListSafe = foldr (uncurry insert) empty

{-# INLINEABLE toList #-}
toList :: Map v -> [(K, v)]
toList (Map l) = l

{-# INLINEABLE lookup #-}

-- | Find an entry in a 'Map'.
lookup :: forall v. K -> Map v -> Maybe v
lookup c (Map xs) =
  let
    go :: [(K, v)] -> Maybe v
    go []              = Nothing
    go ((c', i) : xs') = if c' == c then Just i else go xs'
   in
    go xs

{-# INLINEABLE member #-}
-- | Is the key a member of the map?
member :: forall v. K -> Map v -> Bool
member k m = isJust (lookup k m)

{-# INLINEABLE insert #-}
insert :: forall v. K -> v -> Map v -> Map v
insert k v (Map xs) = Map (go xs)
  where
    go []                = [(k, v)]
    go ((k', v') : rest) = if k == k' then (k, v) : rest else (k', v') : go rest

{-# INLINEABLE delete #-}
delete :: forall v. K -> Map v -> Map v
delete key (Map ls) = Map (go ls)
  where
    go [] = []
    go ((k, v) : rest)
      | k == key = rest
      | otherwise = (k, v) : go rest

{-# INLINEABLE keys #-}
-- | The keys of a 'Map'.
keys :: Map v -> [K]
keys (Map xs) = P.fmap (\(k, _ :: v) -> k) xs

-- | Combine two 'Map's.
union :: forall v r. Map v -> Map r -> Map (These v r)
union (Map ls) (Map rs) =
  let
    f :: v -> Maybe r -> These v r
    f a b' = case b' of
      Nothing -> This a
      Just b  -> These a b

    ls' :: [(K, These v r)]
    ls' = P.fmap (\(c, i) -> (c, f i (lookup c (Map rs)))) ls

    rs' :: [(K, r)]
    rs' = P.filter (\(c, _) -> not (any (\(c', _) -> c' == c) ls)) rs

    rs'' :: [(K, These v r)]
    rs'' = P.fmap (P.fmap That) rs'
   in
    Map (ls' ++ rs'')

{-# INLINEABLE unionWith #-}

-- | Combine two 'Map's with the given combination function.
unionWith :: forall a. (a -> a -> a) -> Map a -> Map a -> Map a
unionWith merge (Map ls) (Map rs) =
  let
    f :: a -> Maybe a -> a
    f a b' = case b' of
      Nothing -> a
      Just b  -> merge a b

    ls' :: [(K, a)]
    ls' = P.fmap (\(c, i) -> (c, f i (lookup c (Map rs)))) ls

    rs' :: [(K, a)]
    rs' = P.filter (\(c, _) -> not (any (\(c', _) -> c' == c) ls)) rs
   in
    Map (ls' ++ rs')

{-# INLINEABLE mapThese #-}

-- | A version of 'Data.Map.Lazy.mapEither' that works with 'These'.
mapThese :: (v -> These a b) -> Map v -> (Map a, Map b)
mapThese f mps = (Map mpl, Map mpr)
  where
    (mpl, mpr) = P.foldr f' ([], []) mps'
    Map mps' = fmap f mps
    f' (k, v) (as, bs) = case v of
      This a    -> ((k, a) : as, bs)
      That b    -> (as, (k, b) : bs)
      These a b -> ((k, a) : as, (k, b) : bs)

-- | A singleton map.
singleton :: K -> v -> Map v
singleton c i = Map [(c, i)]

{-# INLINEABLE empty #-}

-- | An empty 'Map'.
empty :: Map v
empty = Map ([] :: [(K, v)])

{-# INLINEABLE null #-}

-- | Is the map empty?
null :: Map v -> Bool
null = P.null . unMap

{-# INLINEABLE filter #-}

-- | Filter all values that satisfy the predicate.
filter :: (v -> Bool) -> Map v -> Map v
filter f (Map m) = Map $ P.filter (f . snd) m

{-# INLINEABLE elems #-}

-- | Return all elements of the map in the ascending order of their keys.
elems :: Map v -> [v]
elems (Map xs) = P.fmap (\(_ :: K, v) -> v) xs

{-# INLINEABLE mapWithKey #-}

-- | Map a function over all values in the map.
mapWithKey :: (K -> a -> b) -> Map a -> Map b
mapWithKey f (Map xs) = Map $ fmap (\(k, v) -> (k, f k v)) xs

{-# INLINEABLE mapMaybe #-}

-- | Map keys\/values and collect the 'Just' results.
mapMaybe :: (a -> Maybe b) -> Map a -> Map b
mapMaybe f (Map xs) = Map $ P.mapMaybe (\(k, v) -> (k,) <$> f v) xs

{-# INLINEABLE mapMaybeWithKey #-}

-- | Map keys\/values and collect the 'Just' results.
mapMaybeWithKey :: (K -> a -> Maybe b) -> Map a -> Map b
mapMaybeWithKey f (Map xs) = Map $ P.mapMaybe (\(k, v) -> (k,) <$> f k v) xs

{-# INLINEABLE all #-}

-- | Determines whether all elements in the map satisfy the predicate.
all :: (a -> Bool) -> Map a -> Bool
all f (Map m) = go m
  where
    go = \case
      []          -> True
      (_, x) : xs -> if f x then go xs else False

makeLift ''Map
