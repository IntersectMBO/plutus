{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}

module PlutusTx.Data.List (
    List,
    find,
    findIndices,
    filter,
    mapMaybe,
    any,
    foldMap,
) where

import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal (BuiltinList, mkList, unsafeDataAsList)
import PlutusTx.IsData.Class (FromData (..), ToData (..), UnsafeFromData (..))
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude hiding (any, filter, find, findIndices, foldMap, mapMaybe, pred)
import Prettyprinter (Pretty (..))

import Prelude qualified as Haskell

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
    toBuiltinData (List l) = mkList l

instance FromData (List a) where
    {-# INLINEABLE fromBuiltinData #-}
    fromBuiltinData = Just . List . unsafeDataAsList

instance UnsafeFromData (List a) where
    {-# INLINEABLE unsafeFromBuiltinData #-}
    unsafeFromBuiltinData = List . unsafeDataAsList

instance (UnsafeFromData a, Pretty a) => Pretty (List a) where
    {-# INLINEABLE pretty #-}
    pretty = pretty . toSOP

{-# INLINEABLE toSOP #-}
toSOP :: (UnsafeFromData a) => List a -> [a]
toSOP (List l) = go l
  where
    go = B.caseList' [] (\h t -> unsafeFromBuiltinData h : go t)

{-# INLINEABLE find #-}
find :: (UnsafeFromData a) => (a -> Bool) -> List a -> Maybe a
find pred (List l) = go l
  where
    go =
        B.caseList'
            Nothing
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in
                    if pred h'
                        then Just h'
                        else go t
            )

-- TODO: return [] or List?
{-# INLINEABLE findIndices #-}
findIndices :: (UnsafeFromData a) => (a -> Bool) -> List a -> [Integer]
findIndices pred (List l) = go 0 l
  where
    go i =
        B.caseList'
            []
            (\h t ->
                let h' = unsafeFromBuiltinData h
                    indices = go (B.addInteger i 1) t
                in
                    if pred h'
                        then i : indices
                        else indices
            )

-- TODO: return [] or List?
{-# INLINEABLE filter #-}
filter :: (UnsafeFromData a) => (a -> Bool) -> List a -> [a]
filter pred (List l) = go l
  where
    go =
        B.caseList'
            []
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in if pred h' then h' : go t else go t
            )

-- TODO: return [] or List?
{-# INLINEABLE mapMaybe #-}
mapMaybe :: (UnsafeFromData a) => (a -> Maybe b) -> List a -> [b]
mapMaybe f (List l) = go l
  where
    go =
        B.caseList'
            []
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in case f h' of
                    Just b  -> b : go t
                    Nothing -> go t
            )

{-# INLINEABLE any #-}
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

-- TODO: implement Foldable instead
{-# INLINEABLE foldMap #-}
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

makeLift ''List
