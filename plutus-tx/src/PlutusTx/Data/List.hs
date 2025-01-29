{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}

module PlutusTx.Data.List (
    -- constructor exported for testing
    List(List),
    append,
    find,
    findIndices,
    filter,
    mapMaybe,
    any,
    all,
    foldMap,
    map,
    length,
    mconcat,
    fromSOP,
    toSOP,
    toBuiltinList,
    null,
) where

import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal (BuiltinList)
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.IsData.Class (FromData (..), ToData (..), UnsafeFromData (..))
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude hiding (all, any, filter, find, findIndices, foldMap, length, map, mapMaybe,
                         mconcat, null, pred)
import Prettyprinter (Pretty (..))

import Data.Semigroup qualified as Haskell
import Prelude qualified as Haskell

-- | A list type backed directly by 'Data'. It is meant to be used whenever fast
-- encoding/decoding to/from 'Data' is needed.
newtype List a = List (BuiltinList BuiltinData)
  deriving stock (Haskell.Show, Haskell.Eq)

instance Eq (List a) where
    {-# INLINEABLE (==) #-}
    List l == List l' =
        case (B.uncons l, B.uncons l') of
            (Just (h, t), Just (h', t')) -> h == h' && List t == List t'
            (Nothing, Nothing)           -> True
            _                            -> False

instance ToData (List a) where
    {-# INLINEABLE toBuiltinData #-}
    toBuiltinData (List l) = BI.mkList l

instance FromData (List a) where
    {-# INLINEABLE fromBuiltinData #-}
    fromBuiltinData = Just . List . BI.unsafeDataAsList

instance UnsafeFromData (List a) where
    {-# INLINEABLE unsafeFromBuiltinData #-}
    unsafeFromBuiltinData = List . BI.unsafeDataAsList

instance (UnsafeFromData a, Pretty a) => Pretty (List a) where
    {-# INLINEABLE pretty #-}
    pretty = pretty . toSOP

toBuiltinList :: List a -> BuiltinList BuiltinData
toBuiltinList (List l) = l

cons :: (ToData a) => a -> List a -> List a
cons h (List t) = List (BI.mkCons (toBuiltinData h) t)
{-# INLINEABLE cons #-}

{-# INLINEABLE append #-}

append :: List a -> List a -> List a
append (List l) (List l') = List (go l)
  where
    go =
        B.caseList'
            l'
            (\h t -> BI.mkCons h (go t))

instance Semigroup (List a) where
    (<>) = append

instance Monoid (List a) where
    mempty = List B.mkNil

instance Haskell.Semigroup  (List a) where
    (<>) = append

instance Haskell.Monoid (List a) where
    mempty = List B.mkNil

toSOP :: (UnsafeFromData a) => List a -> [a]
toSOP (List l) = go l
  where
    go = B.caseList' [] (\h t -> unsafeFromBuiltinData h : go t)
{-# INLINEABLE toSOP #-}

fromSOP :: (ToData a) => [a] -> List a
fromSOP = List . BI.unsafeDataAsList . B.mkList . fmap toBuiltinData
{-# INLINEABLE fromSOP #-}

find :: (UnsafeFromData a) => (a -> Bool) -> List a -> Maybe a
find pred' (List l) = go l
  where
    go =
        B.caseList'
            Nothing
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in
                    if pred' h'
                        then Just h'
                        else go t
            )
{-# INLINEABLE find #-}

findIndices :: (UnsafeFromData a) => (a -> Bool) -> List a -> List Integer
findIndices pred' (List l) = go 0 l
  where
    go i =
        B.caseList'
            mempty
            (\h t ->
                let h' = unsafeFromBuiltinData h
                    indices = go (B.addInteger 1 i) t
                in
                    if pred' h'
                        then i `cons` indices
                        else indices
            )
{-# INLINEABLE findIndices #-}

filter :: (UnsafeFromData a, ToData a) => (a -> Bool) -> List a -> List a
filter pred (List l) = go l
  where
    go =
        B.caseList'
            mempty
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in if pred h' then h' `cons` go t else go t
            )
{-# INLINEABLE filter #-}

mapMaybe :: (UnsafeFromData a, ToData b) => (a -> Maybe b) -> List a -> List b
mapMaybe f (List l) = go l
  where
    go =
        B.caseList'
            mempty
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in case f h' of
                    Just b  -> b `cons` go t
                    Nothing -> go t
            )
{-# INLINEABLE mapMaybe #-}

any :: (UnsafeFromData a) => (a -> Bool) -> List a -> Bool
any pred (List l) = go l
  where
    go =
        B.caseList'
            False
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in pred h' || go t
            )
{-# INLINEABLE any #-}

all :: (UnsafeFromData a) => (a -> Bool) -> List a -> Bool
all pred (List l) = go l
  where
    go =
        B.caseList'
            True
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in pred h' && go t
            )
{-# INLINEABLE all #-}

foldMap :: (UnsafeFromData a, Monoid m) => (a -> m) -> List a -> m
foldMap f (List l) = go l
  where
    go =
        B.caseList'
            mempty
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in f h' <> go t
            )
{-# INLINEABLE map #-}
map :: (UnsafeFromData a, ToData b) => (a -> b) -> List a -> List b
map f (List l) = List (go l)
  where
    go =
        B.caseList'
            B.mkNil
            (\h t -> BI.mkCons (toBuiltinData $ f $ unsafeFromBuiltinData h) (go t))
{-# INLINEABLE foldMap #-}

length :: List a -> Integer
length (List l) = go l 0
  where
    go =
        B.caseList'
            id
            (\_ t -> B.addInteger 1 . go t)
{-# INLINEABLE length #-}

-- | Plutus Tx version of 'Data.Monoid.mconcat'.
mconcat :: (Monoid a, UnsafeFromData a) => List a -> a
mconcat (List l) = go l
  where
    go =
        B.caseList'
            mempty
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in h' <> go t
            )
{-# INLINABLE mconcat #-}

null :: List a -> Bool
null = B.null . toBuiltinList
{-# INLINABLE null #-}

makeLift ''List
