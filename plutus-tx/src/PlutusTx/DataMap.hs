{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift         #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedLists    #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.DataMap (
  Map,
  singleton,
  empty,
  keys,
  lookup,
  member,
  insert,
  delete,
  union,
  unionWith,
  filter,
  mapMaybe,
  all,
  mapThese,
  map,
  foldr,
  revAppend,
  allPair,
  null,
  foldMapPair,
  foldMap,
  pattern MNil,
  pattern MCons,
) where

import Control.DeepSeq (NFData)
import Data.Data (Data)
import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax as TH (Lift)
import PlutusTx.AsData qualified as AsData
import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.DataList (List (List_), pattern Cons, pattern Nil)
import PlutusTx.DataList qualified as List
import PlutusTx.DataPair (DataElem, Pair, fst, pattern Pair, snd)
import PlutusTx.DataPair qualified as Pair
import PlutusTx.DataThese (These, pattern That, pattern These, pattern This)
import PlutusTx.IsData qualified as P
import PlutusTx.Prelude hiding (all, any, concat, filter, foldMap, foldr, fst, map, null, revAppend,
                         snd, toList)
import Prelude qualified as H

newtype Map k v = Map_ BuiltinData
  deriving stock (Generic, Data, H.Show)
  deriving anyclass (NFData)
  deriving newtype (P.ToData, P.FromData, P.UnsafeFromData)

pattern MNil :: Map k v
pattern MNil <- (Map_ (BI.unsafeDataAsMap -> B.headMaybe -> Nothing))
  where
    MNil = Map_ . BI.mkMap . BI.mkNilPairData $ BI.unitval

pattern MCons :: (DataElem k, DataElem v) => Pair k v -> Map k v -> Map k v
pattern MCons x xs <-
  (Map_
    (BI.unsafeDataAsMap ->
      B.unsafeUncons ->
        (Pair.fromBuiltinPair -> x, BI.mkMap -> Map_ -> xs)
    )
  )
  where
    MCons a (Map_ as) =
      let aPair = Pair.toBuiltinPair a
          builtinList = BI.unsafeDataAsMap as
       in Map_ $ BI.mkMap $ BI.mkCons aPair builtinList

{-# COMPLETE MNil, MCons #-}

-- I think ^ doesn't work because the Data encoding doesn't know that
-- BuiltinList (BuiltinPair BuiltinData BuiltinData) is an instance of BuiltinList BuiltinData
-- also Map is a completely different constructor from List ( this is the actual reason)

instance (DataElem k, DataElem v, Eq k, Semigroup v) =>  Semigroup (Map k v) where
  (<>) = unionWith (<>)

instance (DataElem k, DataElem v, Eq k, Semigroup v) => Monoid (Map k v) where
  mempty = empty

empty :: Map k v
empty = MNil

lookup :: (DataElem k, DataElem v, Eq k) => k -> Map k v -> Maybe v
lookup k =
  \case
    MNil -> Nothing
    MCons x xs ->
      if k == fst x
        then Just . snd $ x
        else lookup k xs

member :: (DataElem k, DataElem v, Eq k) => k -> Map k v -> Bool
member k m =
    case lookup k m of
        Just _  -> True
        Nothing -> False

-- TODO: this possibly could be improved?
toList :: (DataElem k, DataElem v) => Map k v -> List (Pair k v)
toList MNil         = Nil
toList (MCons x xs) = Cons x (toList xs)

-- TODO: this possibly could be improved?
unsafeFromList :: (DataElem k, DataElem v) => List (Pair k v) -> Map k v
unsafeFromList Nil         = MNil
unsafeFromList (Cons x xs) = MCons x (unsafeFromList xs)

delete :: (DataElem k, DataElem v, Eq k) => k -> Map k v -> Map k v
delete key =
  \case
    MNil -> MNil
    (MCons elem@(Pair k v) xs) ->
      if key == k
        then xs
        else MCons elem (delete key xs)

insert :: (DataElem k, DataElem v, Eq k) => k -> v -> Map k v -> Map k v
insert key val =
  \case
    MNil -> singleton key val
    (MCons orig@(Pair k v) xs) ->
      if key == k
        then MCons (Pair key val) xs
        else MCons orig (insert key val xs)

null :: (DataElem k, DataElem v) => Map k v -> Bool
null =
  \case
    MNil -> True
    _ -> False

keys :: (DataElem k, DataElem v) => Map k v -> List k
keys =
  \case
    MNil -> Nil
    (MCons (Pair k _) xs) ->
      Cons k (keys xs)

singleton :: (DataElem k, DataElem v) => k -> v -> Map k v
singleton k v = MCons (Pair k v) MNil

mapPair _ MNil         = MNil
mapPair h (MCons p xs) = MCons (h p) (mapPair h xs)

filter _ MNil = MNil
filter h (MCons p xs) =
  if h p
    then MCons p (filter h xs)
    else filter h xs

any _ MNil = True
any h (MCons p xs) =
  h p || any h xs

concat MNil l         = l
concat (MCons x xs) l = MCons x (concat xs l)

union
    :: forall k v1 v2
    . (DataElem k, DataElem v1, DataElem v2, Eq k)
    => Map k v1 -> Map k v2 -> Map k (These v1 v2)
union ls rs =
  let
    f :: v1 -> Maybe v2 -> These v1 v2
    f a b' = case b' of
      Nothing -> This a
      Just b  -> These a b

    ls' :: Map k (These v1 v2)
    ls' = mapPair (\(Pair c i) -> Pair c (f i (lookup c rs))) ls

    -- Keeps only those keys which don't appear in the left map.
    rs' :: Map k v2
    rs' = filter (\(Pair c _) -> not (any (\(Pair c' _) -> c' == c) ls)) rs

    rs'' :: Map k (These v1 v2)
    rs'' = mapPair (Pair.map That) rs'

   in
    concat ls' rs''

unionWith
  :: forall k a
  . (DataElem k, DataElem a, Eq k)
  => (a -> a -> a) -> Map k a -> Map k a -> Map k a
unionWith merge ls rs =
  let
    f :: a -> Maybe a -> a
    f a b' = case b' of
      Nothing -> a
      Just b  -> merge a b

    ls' :: Map k a
    ls' = mapPair (\(Pair c i) -> Pair c (f i (lookup c rs))) ls

    rs' :: Map k a
    rs' = filter (\(Pair c _) -> not (any (\(Pair c' _) -> c' == c) ls)) rs
   in
    concat ls' rs'

all :: (DataElem k, DataElem v) => (v -> Bool) -> Map k v -> Bool
all f =
  \case
    MNil -> True
    (MCons (Pair _ x) xs) ->
      if f x
        then all f xs
        else False

allPair :: (DataElem k, DataElem v) => (Pair k v -> Bool) -> Map k v -> Bool
allPair f =
  \case
    MNil -> True
    (MCons x xs) ->
      if f x
        then allPair f xs
        else False

mapThese
    :: (DataElem k, DataElem v1, DataElem v2)
    => (v1 -> These v1 v2) -> Map k v1 -> (Map k v1, Map k v2)
mapThese f mps = (unsafeFromList mpl, unsafeFromList mpr)
  where
    (mpl, mpr) = List.foldr f' (Nil, Nil) mps'
    mps' = toList $ map f mps
    f' (Pair k v) (as, bs) = case v of
      This a    -> (Cons (Pair k a) as, bs)
      That b    -> (as, Cons (Pair k b) bs)
      These a b -> (Cons (Pair k a) as, Cons (Pair k b) bs)

map
    :: (DataElem k, DataElem v1, DataElem v2)
    => (v1 -> v2) -> Map k v1 -> Map k v2
map f = mapPair (Pair.map f)

foldr :: (DataElem k, DataElem a) => (a -> b -> b) -> b -> Map k a -> b
foldr f z MNil                  = z
foldr f z (MCons (Pair _ v) xs) = f v (foldr f z xs)

foldrPair :: (DataElem k, DataElem v) => (Pair k v -> b -> b) -> b -> Map k v -> b
foldrPair f z MNil         = z
foldrPair f z (MCons x xs) = f x (foldrPair f z xs)

foldMap :: (DataElem k, DataElem v, Monoid m) => (v -> m) -> Map k v -> m
foldMap f = foldr (\a b -> f a <> b) mempty

foldMapPair :: (DataElem k, DataElem v, Monoid m) => (Pair k v -> m) -> Map k v -> m
foldMapPair f = foldrPair (\a b -> f a <> b) mempty

revAppend MNil a         = a
revAppend (MCons x xs) a = revAppend xs (MCons x a)
