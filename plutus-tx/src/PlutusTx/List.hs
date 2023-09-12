-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.List (
    null,
    map,
    and,
    or,
    any,
    all,
    elem,
    notElem,
    find,
    filter,
    listToMaybe,
    uniqueElement,
    findIndices,
    findIndex,
    foldr,
    foldl,
    reverse,
    zip,
    (++),
    (!!),
    head,
    tail,
    take,
    drop,
    splitAt,
    nub,
    nubBy,
    zipWith,
    dropWhile,
    replicate,
    partition,
    sort,
    sortBy,
    ) where

import PlutusTx.Bool (Bool (..), not, otherwise, (||))
import PlutusTx.Builtins (Integer)
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Eq (Eq, (/=), (==))
import PlutusTx.ErrorCodes
import PlutusTx.Ord (Ord, Ordering (..), compare, (<), (<=))
import PlutusTx.Trace (traceError)
import Prelude (Maybe (..), (.))

{- HLINT ignore -}

{-# INLINABLE null #-}
-- | Test whether a list is empty.
null :: [a] -> Bool
null = \case
    [] -> True
    _  -> False

{-# INLINABLE map #-}
-- | Plutus Tx version of 'Data.List.map'.
--
--   >>> map (\i -> i + 1) [1, 2, 3]
--   [2,3,4]
--
map :: forall a b. (a -> b) -> [a] -> [b]
map f = go
  where
    go :: [a] -> [b]
    go = \case
        []   -> []
        x:xs -> f x : go xs

{-# INLINABLE and #-}
-- | Returns the conjunction of a list of Bools.
and :: [Bool] -> Bool
and = \case
    []     -> True
    x : xs -> if x then and xs else False

{-# INLINABLE or #-}
-- | Returns the disjunction of a list of Bools.
or :: [Bool] -> Bool
or = \case
    []     -> False
    x : xs -> if x then True else or xs

{-# INLINABLE any #-}
-- | Determines whether any element of the structure satisfies the predicate.
any :: forall a. (a -> Bool) -> [a] -> Bool
any f = go
  where
    go :: [a] -> Bool
    go = \case
        []     -> False
        x : xs -> if f x then True else go xs

{-# INLINABLE all #-}
-- | Determines whether all elements of the list satisfy the predicate.
all :: forall a. (a -> Bool) -> [a] -> Bool
all f = go
  where
    go :: [a] -> Bool
    go = \case
        []     -> True
        x : xs -> if f x then go xs else False

{-# INLINABLE elem #-}
-- | Does the element occur in the list?
elem :: Eq a => a -> [a] -> Bool
elem = any . (==)

{-# INLINABLE notElem #-}
-- | The negation of `elem`.
notElem :: Eq a => a -> [a] -> Bool
notElem a = not . elem a

{-# INLINABLE find #-}
-- | Returns the leftmost element matching the predicate, or `Nothing` if there's no such element.
find :: forall a. (a -> Bool) -> [a] -> Maybe a
find f = go
  where
    go :: [a] -> Maybe a
    go = \case
        []     -> Nothing
        x : xs -> if f x then Just x else go xs

{-# INLINABLE foldr #-}
-- | Plutus Tx version of 'Data.List.foldr'.
--
--   >>> foldr (\i s -> s + i) 0 [1, 2, 3, 4]
--   10
--
foldr :: forall a b. (a -> b -> b) -> b -> [a] -> b
foldr f acc = go
  where
    go :: [a] -> b
    go = \case
        []   -> acc
        x:xs -> f x (go xs)

{-# INLINABLE foldl #-}
-- | Plutus Tx velsion of 'Data.List.foldl'.
--
--   >>> foldl (\s i -> s + i) 0 [1, 2, 3, 4]
--   10
--
foldl :: forall a b. (b -> a -> b) -> b -> [a] -> b
foldl f = go
  where
    go :: b -> [a] -> b
    go acc = \case
        []   -> acc
        x:xs -> go (f acc x) xs

{-# INLINABLE (++) #-}
-- | Plutus Tx version of '(Data.List.++)'.
--
--   >>> [0, 1, 2] ++ [1, 2, 3, 4]
--   [0,1,2,1,2,3,4]
--
infixr 5 ++
(++) :: [a] -> [a] -> [a]
(++) l r = foldr (:) r l

{-# INLINABLE filter #-}
-- | Plutus Tx version of 'Data.List.filter'.
--
--   >>> filter (> 1) [1, 2, 3, 4]
--   [2,3,4]
--
filter :: (a -> Bool) -> [a] -> [a]
filter p = foldr (\e xs -> if p e then e:xs else xs) []

{-# INLINABLE listToMaybe #-}
-- | Plutus Tx version of 'Data.List.listToMaybe'.
listToMaybe :: [a] -> Maybe a
listToMaybe []    = Nothing
listToMaybe (x:_) = Just x

{-# INLINABLE uniqueElement #-}
-- | Return the element in the list, if there is precisely one.
uniqueElement :: [a] -> Maybe a
uniqueElement [x] = Just x
uniqueElement _   = Nothing

{-# INLINABLE findIndices #-}
-- | Plutus Tx version of 'Data.List.findIndices'.
findIndices :: (a -> Bool) -> [a] -> [Integer]
findIndices p = go 0
    where
        go i l = case l of
            []     -> []
            (x:xs) -> let indices = go (Builtins.addInteger i 1) xs in if p x then i:indices else indices

{-# INLINABLE findIndex #-}
-- | Plutus Tx version of 'Data.List.findIndex'.
findIndex :: (a -> Bool) -> [a] -> Maybe Integer
findIndex f = go 0
  where
    go i = \case
        []     -> Nothing
        x : xs -> if f x then Just i else go (Builtins.addInteger i 1) xs

{-# INLINABLE (!!) #-}
-- | Plutus Tx version of '(GHC.List.!!)'.
--
--   >>> [10, 11, 12] !! 2
--   12
--
infixl 9 !!
(!!) :: forall a. [a] -> Integer -> a
_   !! n0 | n0 < 0 = traceError negativeIndexError
xs0 !! n0 = go n0 xs0
  where
    go :: Integer -> [a] -> a
    go _ []       = traceError indexTooLargeError
    go n (x : xs) =
        if Builtins.equalsInteger n 0
            then x
            else go (Builtins.subtractInteger n 1) xs

{-# INLINABLE reverse #-}
-- | Plutus Tx version of 'Data.List.reverse'.
reverse :: [a] -> [a]
reverse l = rev l []
  where
    rev []     a = a
    rev (x:xs) a = rev xs (x:a)


{-# INLINABLE zip #-}
-- | Plutus Tx version of 'Data.List.zip'.
zip :: [a] -> [b] -> [(a,b)]
zip []     _bs    = []
zip _as    []     = []
zip (a:as) (b:bs) = (a,b) : zip as bs

{-# INLINABLE head #-}
-- | Plutus Tx version of 'Data.List.head'.
head :: [a] -> a
head []      = traceError headEmptyListError
head (x : _) = x

{-# INLINABLE tail #-}
-- | Plutus Tx version of 'Data.List.tail'.
tail :: [a] -> [a]
tail (_:as) =  as
tail []     =  traceError tailEmptyListError

{-# INLINABLE take #-}
-- | Plutus Tx version of 'Data.List.take'.
take :: Integer -> [a] -> [a]
take n _      | n <= 0 =  []
take _ []              =  []
take n (x:xs)          =  x : take (Builtins.subtractInteger n 1) xs

{-# INLINABLE drop #-}
-- | Plutus Tx version of 'Data.List.drop'.
drop :: Integer -> [a] -> [a]
drop n xs     | n <= 0 = xs
drop _ []              = []
drop n (_:xs)          = drop (Builtins.subtractInteger n 1) xs

{-# INLINABLE splitAt #-}
-- | Plutus Tx version of 'Data.List.splitAt'.
splitAt :: Integer -> [a] -> ([a], [a])
splitAt n xs
  | n <= 0    = ([], xs)
  | otherwise = go n xs
  where
    go :: Integer -> [a] -> ([a], [a])
    go _ []     = ([], [])
    go m (y:ys)
      | m == 1 = ([y], ys)
      | otherwise = case go (Builtins.subtractInteger m 1) ys of
          (zs, ws) -> (y:zs, ws)

{-# INLINABLE nub #-}
-- | Plutus Tx version of 'Data.List.nub'.
nub :: (Eq a) => [a] -> [a]
nub = nubBy (==)

{-# INLINABLE elemBy #-}
-- | Plutus Tx version of 'Data.List.elemBy'.
elemBy :: forall a. (a -> a -> Bool) -> a -> [a] -> Bool
elemBy eq y = go
  where
    go :: [a] -> Bool
    go []     = False
    go (x:xs) =  x `eq` y || go xs

{-# INLINABLE nubBy #-}
-- | Plutus Tx version of 'Data.List.nubBy'.
nubBy :: (a -> a -> Bool) -> [a] -> [a]
nubBy eq l = nubBy' l []
  where
    nubBy' [] _         = []
    nubBy' (y:ys) xs
       | elemBy eq y xs = nubBy' ys xs
       | otherwise      = y : nubBy' ys (y:xs)

{-# INLINABLE zipWith #-}
-- | Plutus Tx version of 'Data.List.zipWith'.
zipWith :: forall a b c. (a -> b -> c) -> [a] -> [b] -> [c]
zipWith f = go
  where
    go :: [a] -> [b] -> [c]
    go [] _          = []
    go _ []          = []
    go (x:xs) (y:ys) = f x y : go xs ys

{-# INLINABLE dropWhile #-}
-- | Plutus Tx version of 'Data.List.dropWhile'.
dropWhile :: forall a. (a -> Bool) -> [a] -> [a]
dropWhile p = go
  where
    go :: [a] -> [a]
    go []          =  []
    go xs@(x:xs')
        | p x       = go xs'
        | otherwise = xs

{-# INLINABLE replicate #-}
-- | Plutus Tx version of 'Data.List.replicate'.
replicate :: forall a. Integer -> a -> [a]
replicate n0 x = go n0 where
    go n | n <= 0 = []
    go n          = x : go (Builtins.subtractInteger n 1)

{-# INLINABLE partition #-}
-- | Plutus Tx version of 'Data.List.partition'.
partition :: (a -> Bool) -> [a] -> ([a],[a])
partition p xs = foldr (select p) ([],[]) xs

select :: (a -> Bool) -> a -> ([a], [a]) -> ([a], [a])
select p x ~(ts,fs) | p x       = (x:ts,fs)
                    | otherwise = (ts, x:fs)

{-# INLINABLE sort #-}
-- | Plutus Tx version of 'Data.List.sort'.
sort :: Ord a => [a] -> [a]
sort = sortBy compare

{-# INLINABLE sortBy #-}
-- | Plutus Tx version of 'Data.List.sortBy'.
sortBy :: (a -> a -> Ordering) -> [a] -> [a]
sortBy cmp l = mergeAll (sequences l)
  where
    sequences (a:b:xs)
      | a `cmp` b == GT = descending b [a]  xs
      | otherwise       = ascending  b (a:) xs
    sequences xs = [xs]

    descending a as (b:bs)
      | a `cmp` b == GT = descending b (a:as) bs
    descending a as bs  = (a:as): sequences bs

    ascending a as (b:bs)
      | a `cmp` b /= GT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs   = let x = as [a]
                          in x : sequences bs

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = let x = merge a b
                          in x : mergePairs xs
    mergePairs xs       = xs

    merge as@(a:as') bs@(b:bs')
      | a `cmp` b == GT = b:merge as  bs'
      | otherwise       = a:merge as' bs
    merge [] bs         = bs
    merge as []         = as
