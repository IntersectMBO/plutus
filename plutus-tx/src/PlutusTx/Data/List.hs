{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}

module PlutusTx.Data.List (
    List,
    toBuiltinList,
    fromBuiltinList,
    toSOP,
    fromSOP,
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
    cons,
    uncons,
    all,
    and,
    or,
    elem,
    notElem,
    foldr,
    foldl,
    concat,
    concatMap,
    listToMaybe,
    uniqueElement,
    findIndex,
    (!!),
    revAppend,
    reverse,
    zip,
    unzip,
    zipWith,
    head,
    last,
    tail,
    take,
    drop,
    dropWhile,
    splitAt,
    elemBy,
    nubBy,
    nub,
    replicate,
    partition,
    sortBy,
    sort
) where

import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal (BuiltinList)
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.IsData.Class (FromData (..), ToData (..), UnsafeFromData (..))
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude (Bool (..), BuiltinData, Eq (..), Integer, Maybe (..), Monoid (..),
                         Ord (..), Ordering, Semigroup (..), fmap, id, not, pure, traceError, ($),
                         (&&), (.), (<$>), (||))
import Prettyprinter (Pretty (..))

import Data.Semigroup qualified as Haskell
import PlutusTx.ErrorCodes (lastEmptyListError)
import PlutusTx.List qualified as SOP
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
{-# INLINEABLE toBuiltinList #-}

fromBuiltinList :: BuiltinList BuiltinData -> List a
fromBuiltinList = List
{-# INLINEABLE fromBuiltinList #-}

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
filter pred1 (List l) = go l
  where
    go =
        B.caseList'
            mempty
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in if pred1 h' then h' `cons` go t else go t
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
any pred1 (List l) = go l
  where
    go =
        B.caseList'
            False
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in pred1 h' || go t
            )
{-# INLINEABLE any #-}

all :: (UnsafeFromData a) => (a -> Bool) -> List a -> Bool
all pred1 (List l) = go l
  where
    go =
        B.caseList'
            True
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in pred1 h' && go t
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
            (\h t ->
                BI.mkCons
                    (toBuiltinData $ f $ unsafeFromBuiltinData h)
                    (go t)
            )
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

elem :: (ToData a) => a -> List a -> Bool
elem x (List l) = go l
  where
    go =
        B.caseList'
            False
            (\h t ->
                toBuiltinData x == h || go t
            )
{-# INLINEABLE elem #-}

notElem :: (ToData a) => a -> List a -> Bool
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

zip :: forall a b . List a -> List b -> List (a, b)
zip (List l1) (List l2) = List $ go l1 l2
  where
    go l1' l2' =
        B.caseList'
            B.mkNil
            (\h1 t1 ->
                B.caseList'
                    B.mkNil
                    (\h2 t2 ->
                        BI.mkCons
                            (toBuiltinData (h1, h2))
                            (go t1 t2)
                    )
                    l2'
            )
            l1'
{-# INLINEABLE zip #-}

unzip :: List (a, b) -> (List a, List b)
unzip (List l) =
    let (l1, l2) = go l
    in (List l1, List l2)
  where
    go =
        B.caseList'
            (B.mkNil, B.mkNil)
            (\h t ->
                let (a, b) = unsafeFromBuiltinData h
                    (as, bs) = go t
                in (a `BI.mkCons` as, b `BI.mkCons` bs)
            )
{-# INLINEABLE unzip #-}

zipWith
    :: (UnsafeFromData a, UnsafeFromData b, ToData c)
    => (a -> b -> c) -> List a -> List b -> List c
zipWith f (List l1) (List l2) = List $ go l1 l2
  where
    go l1' l2' =
        B.caseList'
            B.mkNil
            (\h1 t1 ->
                B.caseList'
                    B.mkNil
                    (\h2 t2 ->
                        BI.mkCons
                            (toBuiltinData
                            $ f
                                (unsafeFromBuiltinData h1)
                                (unsafeFromBuiltinData h2)
                            )
                            (go t1 t2)
                    )
                    l2'
            )
            l1'
{-# INLINEABLE zipWith #-}

head :: (UnsafeFromData a) => List a -> a
head (List l) = unsafeFromBuiltinData $ B.head l
{-# INLINEABLE head #-}

last :: (UnsafeFromData a) => List a -> a
last (List l) = unsafeFromBuiltinData $ go l
  where
    go =
        B.caseList'
            (traceError lastEmptyListError)
            (\h t ->
                if B.null t
                    then h
                    else go t
            )
{-# INLINEABLE last #-}

tail :: List a -> List a
tail (List l) = List $ B.tail l
{-# INLINEABLE tail #-}

take :: Integer -> List a -> List a
take n (List l) = List $ go n l
  where
    go n' =
        B.caseList'
            B.mkNil
            (\h t ->
                if B.equalsInteger n' 0
                    then B.mkNil
                    else BI.mkCons h (go (B.subtractInteger n' 1) t)
            )
{-# INLINEABLE take #-}

drop :: Integer -> List a -> List a
drop n (List l) = List $ go n l
  where
    go n' =
        B.caseList'
            B.mkNil
            (\_ t ->
                if B.equalsInteger n' 0
                    then t
                    else go (B.subtractInteger n' 1) t
            )
{-# INLINEABLE drop #-}

dropWhile :: (UnsafeFromData a) => (a -> Bool) -> List a -> List a
dropWhile pred1 (List l) = List $ go l
  where
    go =
        B.caseList'
            B.mkNil
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in if pred1 h' then go t else l
            )
{-# INLINEABLE dropWhile #-}

splitAt :: Integer -> List a -> (List a, List a)
splitAt n (List l) =
    let (l1, l2) = go n l
    in (List l1, List l2)
  where
    go n' =
        B.caseList'
            (B.mkNil, B.mkNil)
            (\h t ->
                if B.equalsInteger n' 0
                    then (B.mkNil, l)
                    else
                        let (l1, l2) = go (B.subtractInteger n' 1) t
                        in (BI.mkCons h l1, l2)
            )
{-# INLINEABLE splitAt #-}

elemBy :: (UnsafeFromData a) => (a -> a -> Bool) -> a -> List a -> Bool
elemBy pred2 x (List l) = go l
  where
    go =
        B.caseList'
            False
            (\h t ->
                let h' = unsafeFromBuiltinData h
                in pred2 x h' || go t
            )
{-# INLINEABLE elemBy #-}

nubBy :: forall a . (UnsafeFromData a) => (a -> a -> Bool) -> List a -> List a
nubBy pred2 (List l) = List $ go l
  where
    go =
        B.caseList'
            B.mkNil
            (\h t ->
                let h' :: a
                    h' = unsafeFromBuiltinData h
                in if elemBy pred2 h' (List t)
                    then go t
                    else h `BI.mkCons` go t
            )
{-# INLINEABLE nubBy #-}

nub :: (Eq a, UnsafeFromData a) => List a -> List a
nub = nubBy (==)
{-# INLINEABLE nub #-}

replicate :: (ToData a) =>  Integer -> a -> List a
replicate n x = List $ go n
  where
    go n' =
        if B.equalsInteger n' 0
            then B.mkNil
            else BI.mkCons (toBuiltinData x) (go (B.subtractInteger n' 1))
{-# INLINEABLE replicate #-}

partition :: (UnsafeFromData a) => (a -> Bool) -> List a -> (List a, List a)
partition pred1 (List l) =
    let (l1, l2) = go l
    in (List l1, List l2)
  where
    go =
        B.caseList'
            (B.mkNil, B.mkNil)
            (\h t ->
                let h' = unsafeFromBuiltinData h
                    (l1, l2) = go t
                in if pred1 h'
                    then (h `BI.mkCons` l1, l2)
                    else (l1, h `BI.mkCons` l2)
            )
{-# INLINEABLE partition #-}

sortBy
    :: (UnsafeFromData a, ToData a)
    => (a -> a -> Ordering) -> List a -> List a
sortBy cmp l = fromSOP $ SOP.sortBy cmp $ toSOP l
{-# INLINEABLE sortBy #-}

sort :: (Ord a, UnsafeFromData a, ToData a) => List a -> List a
sort = sortBy compare
{-# INLINEABLE sort #-}

makeLift ''List
