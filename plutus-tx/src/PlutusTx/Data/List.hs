{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module PlutusTx.Data.List
  ( List
  , caseList
  , caseList'
  , null
  , append
  , find
  , findIndices
  , filter
  , mapMaybe
  , any
  , all
  , foldMap
  , map
  , length
  , mconcat
  , (<|)
  , cons
  , nil
  , singleton
  , uncons
  , and
  , or
  , elem
  , notElem
  , foldr
  , foldl
  , concat
  , concatMap
  , listToMaybe
  , uniqueElement
  , (!!)
  , revAppend
  , reverse
  , replicate
  , findIndex
  , unzip
  , zipWith
  , head
  , last
  , tail
  , take
  , drop
  , dropWhile
  , splitAt
  , elemBy
  , nubBy
  , nub
  , partition
  , toBuiltinList
  , fromBuiltinList
  , toSOP
  , fromSOP
  ) where

import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal (BuiltinList)
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.IsData.Class (FromData (..), ToData (..), UnsafeFromData (..))
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude
  ( Bool (..)
  , BuiltinData
  , Eq (..)
  , Integer
  , Maybe (..)
  , Monoid (..)
  , Ord (..)
  , Semigroup (..)
  , fmap
  , not
  , pure
  , traceError
  , ($)
  , (&&)
  , (.)
  , (<$>)
  , (||)
  )
import Prettyprinter (Pretty (..))

import Data.Coerce (coerce)
import Data.Semigroup qualified as Haskell
import PlutusTx.ErrorCodes (indexTooLargeError, lastEmptyListError, negativeIndexError)
import Prelude qualified as Haskell

{-| A list type backed directly by 'Data'. It is meant to be used whenever fast
encoding/decoding to/from 'Data' is needed. -}
newtype List a = List (BuiltinList BuiltinData)
  deriving stock (Haskell.Show, Haskell.Eq)

instance Eq (List a) where
  {-# INLINEABLE (==) #-}
  List l == List l' = B.equalsData (BI.mkList l) (BI.mkList l')

instance ToData (List a) where
  {-# INLINEABLE toBuiltinData #-}
  toBuiltinData (List l) = BI.mkList l

instance FromData (List a) where
  {-# INLINEABLE fromBuiltinData #-}
  fromBuiltinData d =
    B.matchData'
      d
      (\_ _ -> Nothing)
      (\_ -> Nothing)
      (Just . List)
      (\_ -> Nothing)
      (\_ -> Nothing)

instance UnsafeFromData (List a) where
  {-# INLINEABLE unsafeFromBuiltinData #-}
  unsafeFromBuiltinData = List . BI.unsafeDataAsList

instance (UnsafeFromData a, Pretty a) => Pretty (List a) where
  {-# INLINEABLE pretty #-}
  pretty = pretty . toSOP

instance Semigroup (List a) where
  (<>) = append
  {-# INLINEABLE (<>) #-}

instance Monoid (List a) where
  mempty = nil
  {-# INLINEABLE mempty #-}

instance Haskell.Semigroup (List a) where
  (<>) = append
  {-# INLINEABLE (<>) #-}

instance Haskell.Monoid (List a) where
  mempty = nil
  {-# INLINEABLE mempty #-}

{- Note [Making arguments non-strict in case and match functions]

A function parameter's strictness is in theory irrelevant to the Plinth compiler.
However, it does affect how GHC compiles the function's callsites to GHC Core.

In the instance of `caseList`/`caseList'`, if `c` is strict, and is passed a function
that calls `caseList`/`caseList'`, GHC will end up creating two mutually recursive
bindings for the application of `caseList`/`caseList'`. Since our inliner currently
does not inline recursive bindings, the additional binding will end up not being
inlined, which can lead to significant performance penalty.
-}

-- | Matching on the given `List`.
caseList
  :: forall a r
   . UnsafeFromData a
  => (() -> r)
  -- ^ Nil case
  -> (a -> List a -> r)
  -- ^ Cons case
  -> List a
  -> r
-- See Note [Making arguments non-strict in case and match functions]
caseList ~n ~c (List l) = B.caseList n (\x -> c (unsafeFromBuiltinData x) . List) l
{-# INLINEABLE caseList #-}

{-| Like `caseList`, except the nil case takes an `r` directly, which is evaluated strictly.
If `r` is an error or expensive computation, consider using `caseList` instead. -}
caseList'
  :: forall a r
   . UnsafeFromData a
  => r
  -- ^ Nil case
  -> (a -> List a -> r)
  -- ^ Cons case
  -> List a
  -> r
-- See Note [Making arguments non-strict in case and match functions]
caseList' ~n ~c (List l) = B.caseList' n (\x -> c (unsafeFromBuiltinData x) . List) l
{-# INLINEABLE caseList' #-}

null :: List a -> Bool
null = B.null . coerce @_ @(BuiltinList BuiltinData)
{-# INLINEABLE null #-}

-- | Prepend an element to the list.
infixr 5 <|

(<|) :: ToData a => a -> List a -> List a
(<|) h = coerce . BI.mkCons (toBuiltinData h) . coerce
{-# INLINEABLE (<|) #-}

-- | Synonym for `<|`.
cons :: ToData a => a -> List a -> List a
cons = (<|)
{-# INLINEABLE cons #-}

-- | Construct an empty list.
nil :: List a
nil = List B.mkNil
{-# INLINEABLE nil #-}

-- | Create a list from a single element.
singleton :: ToData a => a -> List a
singleton a = cons a nil
{-# INLINEABLE singleton #-}

append :: List a -> List a -> List a
append (List l) (List l') = List (go l)
  where
    go =
      B.caseList'
        l'
        (\h t -> BI.mkCons h (go t))
{-# INLINEABLE append #-}

{-| Find the first element that satisfies a predicate.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
find :: UnsafeFromData a => (a -> Bool) -> List a -> Maybe a
find pred' = go
  where
    go =
      caseList'
        Nothing
        ( \h t ->
            if pred' h
              then Just h
              else go t
        )
{-# INLINEABLE find #-}

{-| Find the indices of all elements that satisfy a predicate.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
findIndices :: UnsafeFromData a => (a -> Bool) -> List a -> List Integer
findIndices pred' = go 0
  where
    go i =
      caseList'
        mempty
        ( \h t ->
            let indices = go (B.addInteger 1 i) t
             in if pred' h
                  then i <| indices
                  else indices
        )
{-# INLINEABLE findIndices #-}

{-| Filter a list using a predicate.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
filter :: (UnsafeFromData a, ToData a) => (a -> Bool) -> List a -> List a
filter pred1 = go
  where
    go =
      caseList'
        mempty
        ( \h t ->
            if pred1 h then h <| go t else go t
        )
{-# INLINEABLE filter #-}

{-| Map a function over a list and discard the results that are 'Nothing'.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData', or if the result of applying
'f' is expensive to encode to 'BuiltinData'. -}
mapMaybe :: (UnsafeFromData a, ToData b) => (a -> Maybe b) -> List a -> List b
mapMaybe f = go
  where
    go =
      caseList'
        mempty
        ( \h t ->
            case f h of
              Just b -> b <| go t
              Nothing -> go t
        )
{-# INLINEABLE mapMaybe #-}

{-| Check if any element in the list satisfies a predicate.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
any :: UnsafeFromData a => (a -> Bool) -> List a -> Bool
any pred1 = go
  where
    go =
      caseList'
        False
        (\h t -> pred1 h || go t)
{-# INLINEABLE any #-}

{-| Check if all elements in the list satisfy a predicate.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
all :: UnsafeFromData a => (a -> Bool) -> List a -> Bool
all pred1 = go
  where
    go =
      caseList'
        True
        (\h t -> pred1 h && go t)
{-# INLINEABLE all #-}

{-| Fold a list using a monoid.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
foldMap :: (UnsafeFromData a, Monoid m) => (a -> m) -> List a -> m
foldMap f = go
  where
    go =
      caseList'
        mempty
        (\h t -> f h <> go t)
{-# INLINEABLE foldMap #-}

{-| Map a function over a list.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData', or if the result of applying
'f' is expensive to encode to 'BuiltinData'. -}
map :: (UnsafeFromData a, ToData b) => (a -> b) -> List a -> List b
map f = coerce go
  where
    go =
      caseList'
        B.mkNil
        ( \h t ->
            BI.mkCons
              (toBuiltinData $ f h)
              (go t)
        )
{-# INLINEABLE map #-}

-- | Get the length of a list.
length :: List a -> Integer
length (List l) = go l
  where
    go = BI.caseList' 0 (\_ -> B.addInteger 1 . go)
{-# INLINEABLE length #-}

{-| Concatenate a list of monoids.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
mconcat :: (Monoid a, UnsafeFromData a) => List a -> a
mconcat = go
  where
    go =
      caseList'
        mempty
        (\h t -> h <> go t)
{-# INLINEABLE mconcat #-}

-- | Get the first element of a list and the rest of the list.
uncons :: UnsafeFromData a => List a -> Maybe (a, List a)
uncons (List l) = do
  (h, t) <- B.uncons l
  pure (unsafeFromBuiltinData h, List t)
{-# INLINEABLE uncons #-}

{-| Check if all elements in the list are 'True'.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
and :: List Bool -> Bool
and = go
  where
    go =
      caseList'
        True
        (\h t -> h && go t)
{-# INLINEABLE and #-}

{-| Check if any element in the list is 'True'.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
or :: List Bool -> Bool
or = go . coerce
  where
    go =
      caseList'
        False
        (\h t -> h || go t)
{-# INLINEABLE or #-}

{-| Check if an element is in the list.
Note: this function can leverage the better performance of equality checks
for 'BuiltinData'. -}
elem :: ToData a => a -> List a -> Bool
elem x = go . coerce
  where
    go =
      let x' = toBuiltinData x
       in B.caseList'
            False
            (\h t -> x' == h || go t)
{-# INLINEABLE elem #-}

-- | Check if an element is not in the list.
notElem :: ToData a => a -> List a -> Bool
notElem x = not . elem x
{-# INLINEABLE notElem #-}

{-| Fold a list from the right.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
foldr :: UnsafeFromData a => (a -> b -> b) -> b -> List a -> b
foldr f z = go z . coerce
  where
    go u =
      B.caseList'
        u
        (\h -> f (unsafeFromBuiltinData h) . go u)
{-# INLINEABLE foldr #-}

{-| Fold a list from the left.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
foldl :: UnsafeFromData a => (b -> a -> b) -> b -> List a -> b
foldl f z = go z . coerce
  where
    go acc =
      B.caseList'
        acc
        ( \h t ->
            let h' = unsafeFromBuiltinData h
             in go (f acc h') t
        )
{-# INLINEABLE foldl #-}

-- | Flatten a list of lists into a single list.
concat :: List (List a) -> List a
concat = foldr append mempty
{-# INLINEABLE concat #-}

-- | Map a function over a list and concatenate the results.
concatMap :: UnsafeFromData a => (a -> List b) -> List a -> List b
concatMap = foldMap
{-# INLINEABLE concatMap #-}

-- | Get the first element of a list if it is not empty.
listToMaybe :: UnsafeFromData a => List a -> Maybe a
listToMaybe (List l) = unsafeFromBuiltinData <$> B.headMaybe l
{-# INLINEABLE listToMaybe #-}

-- | Get the element of a list if it has exactly one element.
uniqueElement :: UnsafeFromData a => List a -> Maybe a
uniqueElement (List l) = do
  (h, t) <- B.uncons l
  if B.null t
    then Just $ unsafeFromBuiltinData h
    else Nothing
{-# INLINEABLE uniqueElement #-}

{-| Get the element at a given index.
Warning: this is a partial function and will fail if the index is negative or
greater than the length of the list.
Note: this function has the same precedence as (!!) from 'PlutusTx.List'. -}
infixl 9 !!

(!!) :: UnsafeFromData a => List a -> Integer -> a
(List l) !! n =
  if B.lessThanInteger n 0
    then traceError negativeIndexError
    else go n l
  where
    go n' =
      B.caseList
        (\() -> traceError indexTooLargeError)
        ( \h t ->
            if B.equalsInteger n' 0
              then unsafeFromBuiltinData h
              else go (B.subtractInteger n' 1) t
        )
{-# INLINEABLE (!!) #-}

-- | Append two lists in reverse order.
revAppend :: List a -> List a -> List a
revAppend (List l) (List l') = List $ rev l l'
  where
    rev l1 l2 =
      B.caseList'
        l2
        (\h t -> rev t (BI.mkCons h l2))
        l1
{-# INLINEABLE revAppend #-}

-- | Reverse a list.
reverse :: List a -> List a
reverse l = revAppend l mempty
{-# INLINEABLE reverse #-}

-- | Replicate a value n times.
replicate :: ToData a => Integer -> a -> List a
replicate n (toBuiltinData -> x) = coerce $ go n
  where
    go n' =
      if B.equalsInteger n' 0
        then B.mkNil
        else BI.mkCons x (go (B.subtractInteger n' 1))
{-# INLINEABLE replicate #-}

{-| Find the index of the first element that satisfies a predicate.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
findIndex :: UnsafeFromData a => (a -> Bool) -> List a -> Maybe Integer
findIndex pred' = go 0 . coerce
  where
    go i =
      B.caseList'
        Nothing
        ( \h t ->
            if pred' (unsafeFromBuiltinData h) then Just i else go (B.addInteger 1 i) t
        )
{-# INLINEABLE findIndex #-}

-- | Split a list of pairs into a pair of lists.
unzip :: forall a b. List (a, b) -> (List a, List b)
unzip =
  coerce go
  where
    go :: BuiltinList BuiltinData -> (BuiltinList BuiltinData, BuiltinList BuiltinData)
    go =
      B.caseList'
        (B.mkNil, B.mkNil)
        ( \h t ->
            let (a, b) = unsafeFromBuiltinData h
                (as, bs) = go t
             in (a `BI.mkCons` as, b `BI.mkCons` bs)
        )
{-# INLINEABLE unzip #-}

{-| Zip two lists together using a function.
Warning: this function can be very inefficient if the lists contain elements
that are expensive to decode from 'BuiltinData', or if the result of applying
'f' is expensive to encode to 'BuiltinData'. -}
zipWith
  :: (UnsafeFromData a, UnsafeFromData b, ToData c)
  => (a -> b -> c) -> List a -> List b -> List c
zipWith f = coerce go
  where
    go :: BuiltinList BuiltinData -> BuiltinList BuiltinData -> BuiltinList BuiltinData
    go l1' l2' =
      B.caseList'
        B.mkNil
        ( \h1 t1 ->
            B.caseList'
              B.mkNil
              ( \h2 t2 ->
                  BI.mkCons
                    ( toBuiltinData
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

{-| Return the head of a list.
Warning: this is a partial function and will fail if the list is empty. -}
head :: forall a. UnsafeFromData a => List a -> a
head =
  coerce
    @(BuiltinList BuiltinData -> a)
    @(List a -> a)
    (unsafeFromBuiltinData . B.head)
{-# INLINEABLE head #-}

{-| Return the last element of a list.
Warning: this is a partial function and will fail if the list is empty. -}
last :: forall a. UnsafeFromData a => List a -> a
last =
  coerce
    @(BuiltinList BuiltinData -> a)
    @(List a -> a)
    (unsafeFromBuiltinData . go)
  where
    go :: BuiltinList BuiltinData -> BuiltinData
    go =
      B.caseList
        (\() -> traceError lastEmptyListError)
        ( \h t ->
            if B.null t
              then h
              else go t
        )
{-# INLINEABLE last #-}

{-| Return the tail of a list.
Warning: this is a partial function and will fail if the list is empty. -}
tail :: forall a. List a -> List a
tail = coerce @(BuiltinList BuiltinData) @(List a) . B.tail . coerce
{-# INLINEABLE tail #-}

-- | Take the first n elements from the list.
take :: forall a. Integer -> List a -> List a
take n = coerce $ go n
  where
    go :: Integer -> BuiltinList BuiltinData -> BuiltinList BuiltinData
    go n' =
      B.caseList'
        B.mkNil
        ( \h t ->
            if B.equalsInteger n' 0
              then B.mkNil
              else BI.mkCons h (go (B.subtractInteger n' 1) t)
        )
{-# INLINEABLE take #-}

-- | Drop the first n elements from the list.
drop :: forall a. Integer -> List a -> List a
drop n = coerce $ go n
  where
    go :: Integer -> BuiltinList BuiltinData -> BuiltinList BuiltinData
    go n' xs =
      if n' <= 0
        then xs
        else
          B.caseList'
            B.mkNil
            (\_ -> go (B.subtractInteger n' 1))
            xs
{-# INLINEABLE drop #-}

{-| Drop elements from the list while the predicate holds.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
dropWhile :: forall a. UnsafeFromData a => (a -> Bool) -> List a -> List a
dropWhile pred1 =
  coerce @_ @(List a -> List a) $ go
  where
    go :: BuiltinList BuiltinData -> BuiltinList BuiltinData
    go xs =
      B.caseList'
        B.mkNil
        ( \h t ->
            if pred1 (unsafeFromBuiltinData h) then go t else xs
        )
        xs
{-# INLINEABLE dropWhile #-}

-- | Split a list at a given index.
splitAt :: forall a. Integer -> List a -> (List a, List a)
splitAt n l =
  coerce $ go n (coerce @_ @(BuiltinList BuiltinData) l)
  where
    go n' xs =
      if n' <= 0
        then (B.mkNil, xs)
        else
          B.caseList'
            (B.mkNil, B.mkNil)
            ( \h t ->
                if B.equalsInteger n' 0
                  then (B.mkNil, coerce @_ @(BuiltinList BuiltinData) l)
                  else
                    let (l1, l2) = go (B.subtractInteger n' 1) t
                     in (BI.mkCons h l1, l2)
            )
            xs
{-# INLINEABLE splitAt #-}

{-| Check if an element satisfying a binary predicate is in the list.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
elemBy :: UnsafeFromData a => (a -> a -> Bool) -> a -> List a -> Bool
elemBy pred2 x = go . coerce
  where
    go =
      B.caseList'
        False
        (\h t -> pred2 (unsafeFromBuiltinData h) x || go t)
{-# INLINEABLE elemBy #-}

{-| Removes elements from the list that satisfy a binary predicate.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
nubBy :: forall a. UnsafeFromData a => (a -> a -> Bool) -> List a -> List a
nubBy pred2 l =
  coerce @_ @(List a) $ go (coerce @_ @(BuiltinList BuiltinData) l) B.mkNil
  where
    go ys xs =
      B.caseList'
        B.mkNil
        ( \h t ->
            if elemBy pred2 (unsafeFromBuiltinData h) (coerce xs)
              then go t xs
              else BI.mkCons h (go t (BI.mkCons h xs))
        )
        ys
{-# INLINEABLE nubBy #-}

{-| Removes duplicate elements from the list.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
nub :: (Eq a, UnsafeFromData a) => List a -> List a
nub = nubBy (==)
{-# INLINEABLE nub #-}

{-| Partition a list into two lists based on a predicate.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
partition :: UnsafeFromData a => (a -> Bool) -> List a -> (List a, List a)
partition pred1 l =
  coerce $ go (coerce l)
  where
    go =
      B.caseList'
        (B.mkNil, B.mkNil)
        ( \h t ->
            let h' = unsafeFromBuiltinData h
                (l1, l2) = go t
             in if pred1 h'
                  then (h `BI.mkCons` l1, l2)
                  else (l1, h `BI.mkCons` l2)
        )
{-# INLINEABLE partition #-}

toBuiltinList :: List a -> BuiltinList BuiltinData
toBuiltinList = coerce
{-# INLINEABLE toBuiltinList #-}

fromBuiltinList :: BuiltinList BuiltinData -> List a
fromBuiltinList = coerce
{-# INLINEABLE fromBuiltinList #-}

{-| Convert a data-backed list to a sums of products list.
Warning: this function can be very inefficient if the list contains elements
that are expensive to decode from 'BuiltinData'. -}
toSOP :: forall a. UnsafeFromData a => List a -> [a]
toSOP = coerce go
  where
    go :: BuiltinList BuiltinData -> [a]
    go = B.caseList' [] (\h t -> unsafeFromBuiltinData h : go t)
{-# INLINEABLE toSOP #-}

{-| Convert a sums of products list to a data-backed list.
Warning: this function can be very inefficient if the list contains elements
that are expensive to encode to 'BuiltinData'. -}
fromSOP :: forall a. ToData a => [a] -> List a
fromSOP = coerce . BI.unsafeDataAsList . B.mkList . fmap toBuiltinData
{-# INLINEABLE fromSOP #-}

makeLift ''List
