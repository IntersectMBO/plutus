{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | A map represented as an "association list" of key-value pairs.
module PlutusTx.AssocMap
  ( Map
  , singleton
  , empty
  , null
  , unsafeFromList
  , safeFromList
  , toList
  , keys
  , elems
  , lookup
  , member
  , insert
  , delete
  , union
  , unionWith
  , filter
  , mapWithKey
  , mapMaybe
  , mapMaybeWithKey
  , all
  , mapThese
  ) where

import Prelude qualified as Haskell

import PlutusTx.Builtins qualified as P hiding (null)
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Foldable qualified as F
import PlutusTx.IsData
import PlutusTx.Lift (makeLift)
import PlutusTx.List qualified as List
import PlutusTx.Prelude hiding (mapMaybe)
import PlutusTx.Prelude qualified as P
import PlutusTx.These
import PlutusTx.Traversable

import Control.DeepSeq (NFData)
import Data.Data
import Data.Function (on)
import Data.Kind (Type)
import Data.Map.Strict qualified as HMap
import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax as TH (Lift)
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition.Id (definitionIdFromTypeK)
import PlutusTx.Blueprint.Definition.Unroll (HasBlueprintDefinition (..))
import PlutusTx.Blueprint.Schema (MapSchema (..), Schema (..))
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo)
import Prettyprinter (Pretty (..))

-- See Note [Optimising Value].

{-| A 'Map' of key-value pairs.
A 'Map' is considered well-defined if there are no key collisions, meaning that each value
is uniquely identified by a key.

Use 'safeFromList' to create well-defined 'Map's from arbitrary lists of pairs.

If cost minimisation is required, then you can use 'unsafeFromList' but you must
be certain that the list you are converting to a 'Map' abides by the well-definedness condition.

Most operations on 'Map's are definedness-preserving, meaning that for the resulting 'Map' to be
well-defined then the input 'Map'(s) have to also be well-defined. This is not checked explicitly
unless mentioned in the documentation.

Take care when using 'fromBuiltinData' and 'unsafeFromBuiltinData', as neither function performs
deduplication of the input collection and may create invalid 'Map's! -}
newtype Map k v = Map {unMap :: [(k, v)]}
  deriving stock (Generic, Haskell.Show, Data, TH.Lift)
  deriving newtype (NFData)

instance (Haskell.Ord k, Haskell.Eq v) => Haskell.Eq (Map k v) where
  Map l == Map r =
    on (Haskell.==) HMap.fromList l r

instance (Haskell.Ord k, Haskell.Ord v) => Haskell.Ord (Map k v) where
  Map l <= Map r =
    on (Haskell.<=) HMap.fromList l r

{-| Hand-written instances to use the underlying 'Map' type in 'Data', and
to be reasonably efficient. -}
instance (ToData k, ToData v) => ToData (Map k v) where
  toBuiltinData (Map es) = BI.mkMap (mapToBuiltin es)
    where
      {-# INLINE mapToBuiltin #-}
      mapToBuiltin :: [(k, v)] -> BuiltinList (BuiltinPair BI.BuiltinData BI.BuiltinData)
      mapToBuiltin = go
        where
          go :: [(k, v)] -> BuiltinList (BuiltinPair BI.BuiltinData BI.BuiltinData)
          go [] = P.mkNil
          go ((k, v) : xs) = BI.mkCons (BI.mkPairData (toBuiltinData k) (toBuiltinData v)) (go xs)

{-| A hand-written transformation from 'Data' to 'Map'. Compared to 'unsafeFromBuiltinData',
it is safe to call when it is unknown if the 'Data' is built with 'Data's 'Map' constructor.
Note that it is, however, unsafe in the sense that it assumes that any map
encoded in the 'Data' is well-formed, i.e. 'fromBuiltinData' does not perform any
deduplication of keys or of key-value pairs! -}
instance (FromData k, FromData v) => FromData (Map k v) where
  fromBuiltinData d =
    P.matchData'
      d
      (\_ _ -> Nothing)
      (\es -> Map <$> traverseFromBuiltin es)
      (const Nothing)
      (const Nothing)
      (const Nothing)
      (const Nothing)
    where
      {-# INLINE traverseFromBuiltin #-}
      traverseFromBuiltin
        :: BuiltinList (BuiltinPair BI.BuiltinData BI.BuiltinData)
        -> Maybe [(k, v)]
      traverseFromBuiltin = go
        where
          go :: BuiltinList (BuiltinPair BI.BuiltinData BI.BuiltinData) -> Maybe [(k, v)]
          go =
            P.caseList'
              (pure [])
              ( \tup tups ->
                  liftA2
                    (:)
                    (liftA2 (,) (fromBuiltinData $ BI.fst tup) (fromBuiltinData $ BI.snd tup))
                    (go tups)
              )

{-| A hand-written transformation from 'Data' to 'Map'. It is unsafe because the
caller must provide the guarantee that the 'Data' is constructed using the 'Data's
'Map' constructor.
Note that it assumes, like the 'fromBuiltinData' transformation, that the map
encoded in the 'Data' is well-formed, i.e. 'unsafeFromBuiltinData' does not perform
any deduplication of keys or of key-value pairs! -}
instance (UnsafeFromData k, UnsafeFromData v) => UnsafeFromData (Map k v) where
  -- The `~` here enables `BI.unsafeDataAsMap d` to be inlined, which reduces costs slightly.
  -- Without the `~`, the inliner would consider it not effect safe to inline.
  -- We can remove the `~` once we make the inliner smart enough to inline them.
  -- See https://github.com/IntersectMBO/plutus/pull/5371#discussion_r1297833685
  unsafeFromBuiltinData d = let ~es = BI.unsafeDataAsMap d in Map $ mapFromBuiltin es
    where
      {-# INLINE mapFromBuiltin #-}
      mapFromBuiltin :: BuiltinList (BuiltinPair BI.BuiltinData BI.BuiltinData) -> [(k, v)]
      mapFromBuiltin = go
        where
          go :: BuiltinList (BuiltinPair BI.BuiltinData BI.BuiltinData) -> [(k, v)]
          go =
            P.caseList'
              []
              ( \tup tups ->
                  (unsafeFromBuiltinData $ BI.fst tup, unsafeFromBuiltinData $ BI.snd tup)
                    : go tups
              )

instance
  (HasBlueprintDefinition k, HasBlueprintDefinition v)
  => HasBlueprintDefinition (Map k v)
  where
  type Unroll (Map k v) = [Map k v, k, v]
  definitionId =
    definitionIdFromTypeK @(Type -> Type -> Type) @Map
      Haskell.<> definitionId @k
      Haskell.<> definitionId @v

instance
  ( HasBlueprintSchema k referencedTypes
  , HasBlueprintSchema v referencedTypes
  )
  => HasBlueprintSchema (Map k v) referencedTypes
  where
  schema =
    SchemaMap
      emptySchemaInfo
      MkMapSchema
        { keySchema = schema @k
        , valueSchema = schema @v
        , minItems = Nothing
        , maxItems = Nothing
        }

instance Functor (Map k) where
  {-# INLINEABLE fmap #-}
  fmap f (Map mp) = Map (fmap (fmap f) mp)

instance F.Foldable (Map k) where
  {-# INLINEABLE foldr #-}
  foldr f z (Map mp) = List.foldr (f . snd) z mp

instance Traversable (Map k) where
  {-# INLINEABLE traverse #-}
  traverse f (Map mp) = Map <$> traverse (traverse f) mp

-- This is the "better" instance for Maps that various people
-- have suggested, which merges conflicting entries with
-- the underlying semigroup for values.
instance (Eq k, Semigroup v) => Semigroup (Map k v) where
  (<>) = unionWith (<>)

instance (Eq k, Semigroup v) => Monoid (Map k v) where
  mempty = empty

instance (Pretty k, Pretty v) => Pretty (Map k v) where
  pretty (Map mp) = pretty mp

{-| Unsafely create a 'Map' from a list of pairs. This should _only_ be applied to lists which
have been checked to not contain duplicate keys, otherwise the resulting 'Map' will contain
conflicting entries (two entries sharing the same key).
As usual, the "keys" are considered to be the first element of the pair. -}
unsafeFromList :: [(k, v)] -> Map k v
unsafeFromList = Map
{-# INLINEABLE unsafeFromList #-}

{-| In case of duplicates, this function will keep only one entry (the one that precedes).
In other words, this function de-duplicates the input list. -}
safeFromList :: Eq k => [(k, v)] -> Map k v
safeFromList = List.foldr (uncurry insert) empty
{-# INLINEABLE safeFromList #-}

toList :: Map k v -> [(k, v)]
toList (Map l) = l
{-# INLINEABLE toList #-}

{-| Find an entry in a 'Map'. If the 'Map' is not well-formed (it contains duplicate keys)
then this will return the value of the left-most pair in the underlying list of pairs. -}
lookup :: forall k v. Eq k => k -> Map k v -> Maybe v
lookup c (Map xs) =
  let
    go :: [(k, v)] -> Maybe v
    go [] = Nothing
    go ((c', i) : xs') = if c' == c then Just i else go xs'
   in
    go xs
{-# INLINEABLE lookup #-}

-- | Is the key a member of the map?
member :: forall k v. Eq k => k -> Map k v -> Bool
member k m = isJust (lookup k m)
{-# INLINEABLE member #-}

-- | If a key already exists in the map, its entry will be replaced with the new value.
insert :: forall k v. Eq k => k -> v -> Map k v -> Map k v
insert k v (Map xs) = Map (go xs)
  where
    go [] = [(k, v)]
    go ((k', v') : rest) = if k == k' then (k, v) : rest else (k', v') : go rest
{-# INLINEABLE insert #-}

{-| Delete an entry from the 'Map'. Assumes that the 'Map' is well-formed, i.e. if the
underlying list of pairs contains pairs with duplicate keys then only the left-most
pair will be removed. -}
delete :: forall k v. Eq k => k -> Map k v -> Map k v
delete key (Map ls) = Map (go ls)
  where
    go [] = []
    go ((k, v) : rest)
      | k == key = rest
      | otherwise = (k, v) : go rest
{-# INLINEABLE delete #-}

{-| The keys of a 'Map'. Semantically, the resulting list is only a set if the 'Map'
didn't contain duplicate keys. -}
keys :: Map k v -> [k]
keys (Map xs) = P.fmap (\(k, _ :: v) -> k) xs
{-# INLINEABLE keys #-}

{-| Combine two 'Map's. Keeps both values on key collisions.
Note that well-formedness is only preserved if the two input maps
are also well-formed.
Also, as an implementation detail, in the case that the right map contains
duplicate keys, and there exists a collision between the two maps,
then only the left-most value of the right map will be kept. -}
union :: forall k v r. Eq k => Map k v -> Map k r -> Map k (These v r)
union (Map ls) (Map rs) =
  let
    f :: v -> Maybe r -> These v r
    f a b' = case b' of
      Nothing -> This a
      Just b -> These a b

    ls' :: [(k, These v r)]
    ls' = P.fmap (\(c, i) -> (c, f i (lookup c (Map rs)))) ls

    -- Keeps only those keys which don't appear in the left map.
    rs' :: [(k, r)]
    rs' = List.filter (\(c, _) -> not (List.any (\(c', _) -> c' == c) ls)) rs

    rs'' :: [(k, These v r)]
    rs'' = P.fmap (P.fmap That) rs'
   in
    Map (ls' List.++ rs'')

{-| Combine two 'Map's with the given combination function.
Note that well-formedness of the resulting map depends on the two input maps
being well-formed.
Also, as an implementation detail, in the case that the right map contains
duplicate keys, and there exists a collision between the two maps,
then only the left-most value of the right map will be kept. -}
unionWith :: forall k a. Eq k => (a -> a -> a) -> Map k a -> Map k a -> Map k a
unionWith merge (Map ls) (Map rs) =
  let
    f :: a -> Maybe a -> a
    f a b' = case b' of
      Nothing -> a
      Just b -> merge a b

    ls' :: [(k, a)]
    ls' = P.fmap (\(c, i) -> (c, f i (lookup c (Map rs)))) ls

    rs' :: [(k, a)]
    rs' = List.filter (\(c, _) -> not (List.any (\(c', _) -> c' == c) ls)) rs
   in
    Map (ls' List.++ rs')
{-# INLINEABLE unionWith #-}

-- | A version of 'Data.Map.Lazy.mapEither' that works with 'These'.
mapThese :: (v -> These a b) -> Map k v -> (Map k a, Map k b)
mapThese f mps = (Map mpl, Map mpr)
  where
    (mpl, mpr) = List.foldr f' ([], []) mps'
    Map mps' = fmap f mps
    f' (k, v) (as, bs) = case v of
      This a -> ((k, a) : as, bs)
      That b -> (as, (k, b) : bs)
      These a b -> ((k, a) : as, (k, b) : bs)
{-# INLINEABLE mapThese #-}

-- | A singleton map.
singleton :: k -> v -> Map k v
singleton c i = Map [(c, i)]

-- | An empty 'Map'.
empty :: Map k v
empty = Map ([] :: [(k, v)])
{-# INLINEABLE empty #-}

-- | Is the map empty?
null :: Map k v -> Bool
null = List.null . unMap
{-# INLINEABLE null #-}

-- | Filter all values that satisfy the predicate.
filter :: (v -> Bool) -> Map k v -> Map k v
filter f (Map m) = Map $ List.filter (f . snd) m
{-# INLINEABLE filter #-}

-- | Return all elements of the map.
elems :: Map k v -> [v]
elems (Map xs) = P.fmap (\(_ :: k, v) -> v) xs
{-# INLINEABLE elems #-}

-- | Map a function over all values in the map.
mapWithKey :: (k -> a -> b) -> Map k a -> Map k b
mapWithKey f (Map xs) = Map $ fmap (\(k, v) -> (k, f k v)) xs
{-# INLINEABLE mapWithKey #-}

-- | Map keys\/values and collect the 'Just' results.
mapMaybe :: (a -> Maybe b) -> Map k a -> Map k b
mapMaybe f (Map xs) = Map $ P.mapMaybe (\(k, v) -> (k,) <$> f v) xs
{-# INLINEABLE mapMaybe #-}

-- | Map keys\/values and collect the 'Just' results.
mapMaybeWithKey :: (k -> a -> Maybe b) -> Map k a -> Map k b
mapMaybeWithKey f (Map xs) = Map $ P.mapMaybe (\(k, v) -> (k,) <$> f k v) xs
{-# INLINEABLE mapMaybeWithKey #-}

-- | Determines whether all elements in the map satisfy the predicate.
all :: (a -> Bool) -> Map k a -> Bool
all f (Map m) = go m
  where
    go = \case
      [] -> True
      (_, x) : xs -> if f x then go xs else False
{-# INLINEABLE all #-}

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(makeLift ''Map)
