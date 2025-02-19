{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}

module PlutusTx.Data.List (
    -- constructor exported for testing
    List(List),
    null,
    append,
    find,
    findIndices,
    filter,
    mapMaybe,
    any,
    foldMap,
    map,
    length,
    mconcat,
    fromSOP,
    toSOP,
) where

import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal (BuiltinList, BuiltinPair)
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.IsData.Class (FromData (..), ToData (..), UnsafeFromData (..))
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude (Bool (..), BuiltinData, Eq (..), Integer, Maybe (..), Monoid (..),
                         Semigroup (..), fmap, id, not, pure, ($), (&&), (.), (<$>), (||))
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

null :: List a -> Bool
null (List l) = B.null l
{-# INLINEABLE null #-}

cons :: (ToData a) => a -> List a -> List a
cons h (List t) = List (BI.mkCons (toBuiltinData h) t)
{-# INLINEABLE cons #-}

append :: List a -> List a -> List a
append (List l) (List l') = List (go l)
  where
    go =
        B.caseList'
            l'
            (\h t -> BI.mkCons h (go t))
{-# INLINEABLE append #-}

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

uncons :: (UnsafeFromData a) => List a -> Maybe (a, List a)
uncons (List l) = do
    (h, t) <- B.uncons l
    pure (unsafeFromBuiltinData h, List t)
{-# INLINEABLE uncons #-}

and :: List Bool -> Bool
and (List l) = go l
  where
    go =
        B.caseList'
            True
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in h' && go t
            )
{-# INLINEABLE and #-}

or :: List Bool -> Bool
or (List l) = go l
  where
    go =
        B.caseList'
            False
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in h' || go t
            )
{-# INLINEABLE or #-}

elem :: (UnsafeFromData a, Eq a) => a -> List a -> Bool
elem x (List l) = go l
  where
    go =
        B.caseList'
            False
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in x == h' || go t
            )
{-# INLINEABLE elem #-}

notElem :: (UnsafeFromData a, Eq a) => a -> List a -> Bool
notElem x (List l) = not $ elem x (List l)
{-# INLINEABLE notElem #-}

foldr :: (UnsafeFromData a) => (a -> b -> b) -> b -> List a -> b
foldr f z (List l) = go l z
  where
    go =
        B.caseList'
            id
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in f h' . go t
            )
{-# INLINEABLE foldr #-}

foldl :: (UnsafeFromData a) => (b -> a -> b) -> b -> List a -> b
foldl f z (List l) = go z l
  where
    go acc =
        B.caseList'
            z
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in go (f acc h') t
            )
{-# INLINEABLE foldl #-}

concat :: List (List a) -> List a
concat = foldr append mempty
{-# INLINEABLE concat #-}

concatMap :: (UnsafeFromData a) => (a -> List b) -> List a -> List b
concatMap = foldMap
{-# INLINEABLE concatMap #-}

listToMaybe :: (UnsafeFromData a) => List a -> Maybe a
listToMaybe (List l) = unsafeFromBuiltinData <$> B.headMaybe l
{-# INLINEABLE listToMaybe #-}

uniqueElement :: (UnsafeFromData a) => List a -> Maybe a
uniqueElement (List l) = do
    (h, t) <- B.uncons l
    if B.null t
        then Just $ unsafeFromBuiltinData h
        else Nothing
{-# INLINEABLE uniqueElement #-}

findIndex :: (UnsafeFromData a) => (a -> Bool) -> List a -> Maybe Integer
findIndex pred' (List l) = go 0 l
  where
    go i =
        B.caseList'
            Nothing
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in if pred' h' then Just i else go (B.addInteger 1 i) t
            )
{-# INLINEABLE findIndex #-}

infixl 9 !!
(!!) :: (UnsafeFromData a) => List a -> Integer -> Maybe a
(!!) (List l) i = go i l
  where
    go n =
        B.caseList'
            Nothing
            (\h t ->
                if B.equalsInteger n 0
                    then Just $ unsafeFromBuiltinData h
                    else go (B.subtractInteger n 1) t
            )
{-# INLINEABLE (!!) #-}

revAppend :: List a -> List a -> List a
revAppend (List l) (List l') = List $ rev l l'
  where
    rev l1 l2 =
        B.caseList'
            l2
            (\h t -> rev (BI.mkCons h l1) t)
            l1
{-# INLINEABLE revAppend #-}

reverse :: List a -> List a
reverse l = revAppend l mempty
{-# INLINEABLE reverse #-}

-- TODO: I don't think there's a sensible way to implement zip


makeLift ''List
