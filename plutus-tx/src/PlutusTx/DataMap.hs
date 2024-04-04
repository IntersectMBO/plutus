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

module PlutusTx.DataMap where

import Control.DeepSeq (NFData)
import Data.Data (Data)
import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax as TH (Lift)
import PlutusTx.AsData qualified as AsData
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.DataList (List (List_), pattern Cons, pattern Nil)
import PlutusTx.DataList qualified as List
import PlutusTx.DataPair (DataElem, Pair, fst, pattern Pair, snd)
import PlutusTx.DataPair qualified as Pair
import PlutusTx.DataThese (These, pattern That, pattern These, pattern This)
import PlutusTx.IsData qualified as P
import PlutusTx.Prelude hiding (foldr, fst, map, snd)
import Prelude qualified as H

newtype Map k v = Map_ BuiltinData
  deriving stock (Generic, Data, H.Show)
  deriving anyclass (NFData)
  deriving newtype (P.ToData, P.FromData, P.UnsafeFromData)

pattern Map :: List (Pair k v) -> Map k v
pattern Map l <- Map_ (BI.unsafeDataAsMap -> BI.mkMap -> List_ -> l)
  where
    Map l = Map_ . P.toBuiltinData $ l

{-# COMPLETE Map #-}

-- I think ^ doesn't work because the Data encoding doesn't know that
-- BuiltinList (BuiltinPair BuiltinData BuiltinData) is an instance of BuiltinList BuiltinData

instance (DataElem k, DataElem v, Eq k, Semigroup v) =>  Semigroup (Map k v) where
  (<>) = unionWith (<>)

instance (DataElem k, DataElem v, Eq k, Semigroup v) => Monoid (Map k v) where
  mempty = empty

empty :: Map k v
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
    :: forall k v1 v2
    . (DataElem k, DataElem v1, DataElem v2, Eq k)
    => Map k v1 -> Map k v2 -> Map k (These v1 v2)
union (Map ls) (Map rs) =
  let
    f :: v1 -> Maybe v2 -> These v1 v2
    f a b' = case b' of
      Nothing -> This a
      Just b  -> These a b

    ls' :: List (Pair k (These v1 v2))
    ls' = List.map (\(Pair c i) -> Pair c (f i (lookup c (Map rs)))) ls

    -- Keeps only those keys which don't appear in the left map.
    rs' :: List (Pair k v2)
    rs' = List.filter (\(Pair c _) -> not (List.any (\(Pair c' _) -> c' == c) ls)) rs

    rs'' :: List (Pair k (These v1 v2))
    rs'' = List.map (Pair.map That) rs'
   in
    Map (ls' <> rs'')

unionWith
  :: forall k a
  . (DataElem k, DataElem a, Eq k)
  => (a -> a -> a) -> Map k a -> Map k a -> Map k a
unionWith merge (Map ls) (Map rs) =
  let
    f :: a -> Maybe a -> a
    f a b' = case b' of
      Nothing -> a
      Just b  -> merge a b

    ls' :: List (Pair k a)
    ls' = List.map (\(Pair c i) -> Pair c (f i (lookup c (Map rs)))) ls

    rs' :: List (Pair k a)
    rs' = List.filter (\(Pair c _) -> not (List.any (\(Pair c' _) -> c' == c) ls)) rs
   in
    Map (ls' <> rs')

all :: (DataElem k, DataElem v) => (v -> Bool) -> Map k v -> Bool
all f (Map m) = go m
  where
    go = \case
      Nil -> True
      (Cons (Pair _ x) xs) -> if f x then go xs else False

mapThese
    :: (DataElem k, DataElem v1, DataElem v2)
    => (v1 -> These v1 v2) -> Map k v1 -> (Map k v1, Map k v2)
mapThese f mps = (Map mpl, Map mpr)
  where
    (mpl, mpr) = List.foldr f' (Nil, Nil) mps'
    Map mps' = map f mps
    f' (Pair k v) (as, bs) = case v of
      This a    -> (Cons (Pair k a) as, bs)
      That b    -> (as, Cons (Pair k b) bs)
      These a b -> (Cons (Pair k a) as, Cons (Pair k b) bs)

map
    :: (DataElem k, DataElem v1, DataElem v2)
    => (v1 -> v2) -> Map k v1 -> Map k v2
map f (Map l) = Map $ List.map (Pair.map f) l

foldr :: (DataElem k, DataElem a) => (a -> b -> b) -> b -> Map k a -> b
foldr f z (Map mp) = List.foldr (f . snd) z mp

foldMap :: (DataElem k, DataElem v, Monoid m) => (v -> m) -> Map k v -> m
foldMap f = foldr (\a b -> f a <> b) mempty
