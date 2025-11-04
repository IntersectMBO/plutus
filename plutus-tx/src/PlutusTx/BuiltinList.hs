{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant if" #-}

-- | Functions operating on `BuiltinList`.
module PlutusTx.BuiltinList (
  BuiltinList,
  cons,
  uncons,
  empty,
  singleton,
  null,
  caseList',
  caseList,
  map,
  elem,
  find,
  any,
  all,
  (!!),
  (++),
  (<|),
  append,
  findIndices,
  filter,
  mapMaybe,
  length,
  and,
  or,
  notElem,
  foldr,
  foldl,
  concat,
  concatMap,
  listToMaybe,
  uniqueElement,
  revAppend,
  reverse,
  replicate,
  findIndex,
  head,
  last,
  tail,
  take,
  drop,
  dropWhile,
  elemBy,
  nub,
  nubBy,
  zipWith,
) where

import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.HasOpaque
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Eq
import PlutusTx.ErrorCodes
import PlutusTx.Ord
import PlutusTx.Prelude hiding (mapMaybe)

-- | Plutus Tx version of 'Data.List.:' for 'BuiltinList'.
cons :: forall a. a -> BuiltinList a -> BuiltinList a
cons = BI.mkCons
{-# INLINEABLE cons #-}

-- | Infix version of 'cons'.
infixr 5 <|

(<|) :: forall a. a -> BuiltinList a -> BuiltinList a
(<|) = cons
{-# INLINEABLE (<|) #-}

-- | Plutus Tx version of 'Data.List.uncons' for 'BuiltinList'.
uncons :: forall a. BuiltinList a -> Maybe (a, BuiltinList a)
uncons = B.uncons
{-# INLINEABLE uncons #-}

-- | Plutus Tx version of '[]' for 'BuiltinList'.
empty :: forall a. (MkNil a) => BuiltinList a
empty = B.mkNil
{-# INLINEABLE empty #-}

-- | Plutus Tx version of 'Data.List.null' for 'BuiltinList'.
null :: forall a. BuiltinList a -> Bool
null = B.null
{-# INLINEABLE null #-}

-- | Make a list with one element.
singleton :: forall a. (MkNil a) => a -> BuiltinList a
singleton x = x <| empty
{-# INLINEABLE singleton #-}

caseList' :: forall a r. r -> (a -> BuiltinList a -> r) -> BuiltinList a -> r
caseList' = B.caseList'
{-# INLINEABLE caseList' #-}

caseList :: forall a r. (() -> r) -> (a -> BuiltinList a -> r) -> BuiltinList a -> r
caseList = B.caseList
{-# INLINEABLE caseList #-}

-- | Plutus Tx version of 'Data.List.map' for 'BuiltinList'.
map :: forall a b. (MkNil b) => (a -> b) -> BuiltinList a -> BuiltinList b
map f = go
 where
  go :: BuiltinList a -> BuiltinList b
  go = caseList' empty (\x xs -> f x <| go xs)
{-# INLINEABLE map #-}

-- | Plutus Tx version of 'Data.List.mapMaybe' for 'BuiltinList'.
mapMaybe :: forall a b. (MkNil b) => (a -> Maybe b) -> BuiltinList a -> BuiltinList b
mapMaybe f = go
 where
  go :: BuiltinList a -> BuiltinList b
  go =
    caseList'
      empty
      ( \x xs -> case f x of
          Nothing -> go xs
          Just y  -> y <| go xs
      )
{-# INLINEABLE mapMaybe #-}

-- | Does the element occur in the list?
elem :: forall a. (Eq a) => a -> BuiltinList a -> Bool
elem a = go
 where
  go :: BuiltinList a -> Bool
  go = caseList' False (\x xs -> if a == x then True else go xs)
{-# INLINEABLE elem #-}

-- | Returns the leftmost element matching the predicate, or `Nothing` if there's no such element.
find :: forall a. (a -> Bool) -> BuiltinList a -> Maybe a
find p = go
 where
  go :: BuiltinList a -> Maybe a
  go = caseList' Nothing (\x xs -> if p x then Just x else go xs)
{-# INLINEABLE find #-}

-- | Determines whether any element of the structure satisfies the predicate.
any :: forall a. (a -> Bool) -> BuiltinList a -> Bool
any p = go
 where
  go :: BuiltinList a -> Bool
  go = caseList' False (\x xs -> if p x then True else go xs)
{-# INLINEABLE any #-}

-- | Determines whether all elements of the list satisfy the predicate.
all :: forall a. (a -> Bool) -> BuiltinList a -> Bool
all p = go
 where
  go :: BuiltinList a -> Bool
  go = caseList' True (\x xs -> if p x then go xs else False)
{-# INLINEABLE all #-}

{-| Get the element at a given index.
This function throws an error if the index is negative or larger than the length
of the list.
-}
infixl 9 !!

(!!) :: forall a. BuiltinList a -> Integer -> a
(!!) xs i
  | i `B.lessThanInteger` 0 = traceError builtinListNegativeIndexError
  | otherwise =
      B.caseList
        (\_ann -> traceError builtinListIndexTooLargeError)
        (\y _rest _ann -> y)
        (BI.drop i xs)
        ()
{-# INLINEABLE (!!) #-}

-- | Plutus Tx version of 'Data.List.length' for 'BuiltinList'.
length :: forall a. BuiltinList a -> Integer
length = foldr (\_ -> B.addInteger 1) 0
{-# INLINEABLE length #-}

-- | Returns the conjunction of a list of Bools.
and :: BuiltinList Bool -> Bool
and = all (\x -> BI.ifThenElse x True False)

-- | Returns the disjunction of a list of Bools.
or :: BuiltinList Bool -> Bool
or = any (\x -> BI.ifThenElse x True False)
{-# INLINEABLE or #-}

-- | The negation of `elem`.
notElem :: forall a. (Eq a) => a -> BuiltinList a -> Bool
notElem a = not . elem a
{-# INLINEABLE notElem #-}

-- | Plutus Tx version of 'Data.List.foldr' for 'BuiltinList'.
foldr :: forall a b. (a -> b -> b) -> b -> BuiltinList a -> b
foldr f acc = go
 where
  go :: BuiltinList a -> b
  go = caseList' acc (\x xs -> f x (go xs))
{-# INLINEABLE foldr #-}

-- | Plutus Tx velsion of 'Data.List.foldl' for 'BuiltinList'.
foldl :: forall a b. (b -> a -> b) -> b -> BuiltinList a -> b
foldl f = go
 where
  go :: b -> BuiltinList a -> b
  go acc = caseList' acc (\x xs -> go (f acc x) xs)
{-# INLINEABLE foldl #-}

-- | Plutus Tx version of '(Data.List.++)' for 'BuiltinList'.
infixr 5 ++

(++) :: forall a. BuiltinList a -> BuiltinList a -> BuiltinList a
(++) l r = foldr (<|) r l
{-# INLINEABLE (++) #-}

-- | Plutus Tx version of 'Data.List.append' for 'BuiltinList'.
append :: forall a. BuiltinList a -> BuiltinList a -> BuiltinList a
append = (++)
{-# INLINEABLE append #-}

-- | Plutus Tx version of 'Data.List.concat' for 'BuiltinList'.
concat :: forall a. (MkNil a) => BuiltinList (BuiltinList a) -> BuiltinList a
concat = foldr (++) empty
{-# INLINEABLE concat #-}

-- | Plutus Tx version of 'Data.List.concatMap' for 'BuiltinList'.
concatMap :: forall a b. (MkNil b) => (a -> BuiltinList b) -> BuiltinList a -> BuiltinList b
concatMap f = foldr (\x ys -> f x ++ ys) empty
{-# INLINEABLE concatMap #-}

-- | Plutus Tx version of 'Data.List.filter' for 'BuiltinList'.
filter :: forall a. (MkNil a) => (a -> Bool) -> BuiltinList a -> BuiltinList a
filter p = foldr (\x xs -> if p x then x <| xs else xs) empty
{-# INLINEABLE filter #-}

-- | Plutus Tx version of 'Data.List.listToMaybe' for 'BuiltinList'.
listToMaybe :: forall a. BuiltinList a -> Maybe a
listToMaybe = caseList' Nothing (\x _ -> Just x)
{-# INLINEABLE listToMaybe #-}

-- | Return the element in the list, if there is precisely one.
uniqueElement :: forall a. BuiltinList a -> Maybe a
uniqueElement =
  caseList'
    Nothing
    (\x -> caseList' (Just x) (\_ _ -> Nothing))
{-# INLINEABLE uniqueElement #-}

-- | Plutus Tx version of 'Data.List.findIndices' for 'BuiltinList'.
findIndices :: forall a. (a -> Bool) -> BuiltinList a -> BuiltinList Integer
findIndices p = go 0
 where
  go :: Integer -> BuiltinList a -> BuiltinList Integer
  go i =
    caseList'
      empty
      ( \x xs ->
          let indices = go (B.addInteger i 1) xs
           in if p x then i <| indices else indices
      )
{-# INLINEABLE findIndices #-}

-- | Plutus Tx version of 'Data.List.findIndex'.
findIndex :: forall a. (a -> Bool) -> BuiltinList a -> Maybe Integer
findIndex f = go 0
 where
  go :: Integer -> BuiltinList a -> Maybe Integer
  go i =
    caseList'
      Nothing
      (\x xs -> if f x then Just i else go (B.addInteger i 1) xs)
{-# INLINEABLE findIndex #-}

{-| Cons each element of the first list to the second one in reverse order
(i.e. the last element of the first list is the head of the result).

> revAppend xs ys === reverse xs ++ ys
-}
revAppend :: forall a. BuiltinList a -> BuiltinList a -> BuiltinList a
revAppend l r = caseList' r (\x xs -> revAppend xs (x <| r)) l
{-# INLINEABLE revAppend #-}

-- | Plutus Tx version of 'Data.List.reverse' for 'BuiltinList'.
reverse :: forall a. (MkNil a) => BuiltinList a -> BuiltinList a
reverse xs = revAppend xs empty
{-# INLINEABLE reverse #-}

-- | Plutus Tx version of 'Data.List.zip' for 'BuiltinList'.
_zip
  :: forall a b
   . (MkNil a, MkNil b)
  => BuiltinList a
  -> BuiltinList b
  -> BuiltinList (BuiltinPair a b)
_zip = zipWith (curry BI.BuiltinPair)
{-# INLINEABLE _zip #-}

-- | Plutus Tx version of 'Data.List.unzip' for 'BuiltinList'.
_unzip
  :: forall a b
   . (MkNil a, MkNil b)
  => BuiltinList (BuiltinPair a b)
  -> BuiltinPair (BuiltinList a) (BuiltinList b)
_unzip =
  caseList'
    emptyPair
    ( \p l -> do
        let x = BI.fst p
        let y = BI.snd p
        let l' = _unzip l
        let xs' = BI.fst l'
        let ys' = BI.snd l'
        BI.BuiltinPair (x <| xs', y <| ys')
    )
 where
  emptyPair :: BuiltinPair (BuiltinList a) (BuiltinList b)
  emptyPair = BI.BuiltinPair (empty, empty)
{-# INLINEABLE _unzip #-}

-- | Plutus Tx version of 'Data.List.head' for 'BuiltinList'.
head :: forall a. BuiltinList a -> a
head =
  caseList
    (\_ -> traceError headEmptyBuiltinListError)
    (\x _ -> x)
{-# INLINEABLE head #-}

-- | Plutus Tx version of 'Data.List.last' for 'BuiltinList'.
last :: forall a. BuiltinList a -> a
last =
  caseList
    (\_ -> traceError lastEmptyBuiltinListError)
    (\x xs -> caseList' x (\_ _ -> last xs) xs)
{-# INLINEABLE last #-}

-- | Plutus Tx version of 'Data.List.tail' for 'BuiltinList'.
tail :: forall a. BuiltinList a -> BuiltinList a
tail = caseList (\_ -> traceError lastEmptyBuiltinListError) (\_ xs -> xs)
{-# INLINEABLE tail #-}

-- | Plutus Tx version of 'Data.List.take' for 'BuiltinList'.
take :: forall a. (MkNil a) => Integer -> BuiltinList a -> BuiltinList a
take n l
  | n `B.lessThanEqualsInteger` 0 = empty
  | otherwise =
      caseList'
        empty
        (\x xs -> x <| take (B.subtractInteger n 1) xs)
        l
{-# INLINEABLE take #-}

-- | Plutus Tx version of 'Data.List.drop' for 'BuiltinList'.
drop :: forall a. (MkNil a) => Integer -> BuiltinList a -> BuiltinList a
drop n l
  | n `B.lessThanEqualsInteger` 0 = l
  | otherwise =
      caseList'
        empty
        (\_ xs -> drop (B.subtractInteger n 1) xs)
        l
{-# INLINEABLE drop #-}

-- | Plutus Tx version of 'Data.List.splitAt' for 'BuiltinList'.
_splitAt
  :: forall a
   . (MkNil a)
  => Integer
  -> BuiltinList a
  -> BuiltinPair (BuiltinList a) (BuiltinList a)
_splitAt n xs
  | n `B.lessThanEqualsInteger` 0 = BI.BuiltinPair (empty, xs)
  | B.null xs = BI.BuiltinPair (empty, empty)
  | otherwise = do
      let (x, xs') = B.unsafeUncons xs
      let BI.BuiltinPair (xs'', xs''') = _splitAt (n `B.subtractInteger` 1) xs'
      BI.BuiltinPair (x <| xs'', xs''')
{-# INLINEABLE _splitAt #-}

-- | Plutus Tx version of 'Data.List.nub' for 'BuiltinList'.
nub :: forall a. (Eq a, MkNil a) => BuiltinList a -> BuiltinList a
nub = nubBy (==)
{-# INLINEABLE nub #-}

-- | Plutus Tx version of 'Data.List.elemBy' for 'BuiltinList'.
elemBy :: forall a. (a -> a -> Bool) -> a -> BuiltinList a -> Bool
elemBy eq y = go
 where
  go :: BuiltinList a -> Bool
  go = caseList' False (\x xs -> if eq x y then True else go xs)
{-# INLINEABLE elemBy #-}

-- | Plutus Tx version of 'Data.List.nubBy' for 'BuiltinList'.
nubBy :: forall a. (MkNil a) => (a -> a -> Bool) -> BuiltinList a -> BuiltinList a
nubBy eq = flip go empty
 where
  go :: BuiltinList a -> BuiltinList a -> BuiltinList a
  go l xs =
    caseList'
      empty
      ( \y ys ->
          if elemBy eq y xs
            then go ys xs
            else y <| go ys (y <| xs)
      )
      l
{-# INLINEABLE nubBy #-}

-- | Plutus Tx version of 'Data.List.zipWith' for 'BuiltinList'.
zipWith
  :: forall a b c
   . (MkNil c)
  => (a -> b -> c)
  -> BuiltinList a
  -> BuiltinList b
  -> BuiltinList c
zipWith f = go
 where
  go :: BuiltinList a -> BuiltinList b -> BuiltinList c
  go xs ys =
    caseList'
      empty
      ( \x xs' ->
          caseList'
            empty
            (\y ys' -> f x y <| go xs' ys')
            ys
      )
      xs
{-# INLINEABLE zipWith #-}

-- | Plutus Tx version of 'Data.List.dropWhile' for 'BuiltinList'.
dropWhile :: forall a. (a -> Bool) -> BuiltinList a -> BuiltinList a
dropWhile p = go
 where
  go :: BuiltinList a -> BuiltinList a
  go xs = caseList' xs (\x xs' -> if p x then go xs' else xs) xs
{-# INLINEABLE dropWhile #-}

-- | Plutus Tx version of 'Data.List.replicate' for 'BuiltinList'.
replicate :: forall a. (MkNil a) => Integer -> a -> BuiltinList a
replicate n0 x = go n0
 where
  go :: Integer -> BuiltinList a
  go n
    | n `B.lessThanEqualsInteger` 0 = empty
    | otherwise = x <| go (B.subtractInteger n 1)
{-# INLINEABLE replicate #-}

-- | Plutus Tx version of 'Data.List.partition' for 'BuiltinList'.
_partition
  :: forall a
   . (MkNil a)
  => (a -> Bool)
  -> BuiltinList a
  -> BuiltinPair (BuiltinList a) (BuiltinList a)
_partition p = BI.BuiltinPair . foldr select (empty, empty)
 where
  select :: a -> (BuiltinList a, BuiltinList a) -> (BuiltinList a, BuiltinList a)
  select x ~(ts, fs) = if p x then (x <| ts, fs) else (ts, x <| fs)
{-# INLINEABLE _partition #-}

-- | Plutus Tx version of 'Data.List.sort' for 'BuiltinList'.
_sort :: (MkNil a, Ord a) => BuiltinList a -> BuiltinList a
_sort = _sortBy compare
{-# INLINEABLE _sort #-}

-- | Plutus Tx version of 'Data.List.sortBy' for 'BuiltinList'.
_sortBy :: (MkNil a) => (a -> a -> Ordering) -> BuiltinList a -> BuiltinList a
_sortBy cmp = mergeAll . sequences
 where
  sequences = caseList'' empty (singleton . singleton) f
   where
    f a b xs
      | a `cmp` b == GT = descending b (singleton a) xs
      | otherwise = ascending b (cons a) xs

  descending a as l = caseList' d f l
   where
    d = (a <| as) <| sequences l
    f b bs
      | a `cmp` b == GT = descending b (a <| as) bs
      | otherwise = d

  ascending a as l = caseList' d f l
   where
    d = as (singleton a) <| sequences l
    f b bs
      | a `cmp` b /= GT = ascending b (as . cons a) bs
      | otherwise = d

  mergeAll l =
    case uniqueElement l of
      Nothing ->
        mergeAll (mergePairs l)
      Just x ->
        x

  mergePairs = caseList'' empty singleton f
   where
    f a b xs = merge a b <| mergePairs xs

  merge as bs
    | null as = bs
    | null bs = as
    | otherwise = do
        let a = head as
        let b = head bs
        let as' = tail as
        let bs' = tail bs
        if a `cmp` b == GT
          then
            b <| merge as bs'
          else
            a <| merge as' bs

  caseList'' :: forall a r. r -> (a -> r) -> (a -> a -> BuiltinList a -> r) -> BuiltinList a -> r
  caseList'' f0 f1 f2 = caseList' f0 (\x xs -> caseList' (f1 x) (\y ys -> f2 x y ys) xs)
{-# INLINEABLE _sortBy #-}
