{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.List (
    map,
    filter,
    listToMaybe,
    uniqueElement,
    findIndices,
    findIndex,
    foldr,
    reverse,
    zip,
    (++),
    (!!),
    head,
    take,
    tail,
    nub,
    nubBy,
    zipWith,
    dropWhile,
    partition,
    sort,
    sortBy
    ) where

import PlutusTx.Bool (Bool (..), otherwise, (||))
import PlutusTx.Builtins (Integer)
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Eq (Eq, (/=), (==))
import PlutusTx.ErrorCodes
import PlutusTx.Ord (Ord, Ordering (..), compare, (<), (<=))
import PlutusTx.Trace (traceError)
import Prelude (Maybe (..))

{- HLINT ignore -}

{-# INLINABLE map #-}
-- | Plutus Tx version of 'Data.List.map'.
--
--   >>> map (\i -> i + 1) [1, 2, 3]
--   [2,3,4]
--
map :: (a -> b) -> [a] -> [b]
map f l = case l of
    []   -> []
    x:xs -> f x : map f xs

{-# INLINABLE foldr #-}
-- | Plutus Tx version of 'Data.List.foldr'.
--
--   >>> foldr (\i s -> s + i) 0 [1, 2, 3, 4]
--   10
--
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f acc l = case l of
    []   -> acc
    x:xs -> f x (foldr f acc xs)

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
findIndex p l = listToMaybe (findIndices p l)

{-# INLINABLE (!!) #-}
-- | Plutus Tx version of '(GHC.List.!!)'.
--
--   >>> [10, 11, 12] !! 2
--   12
--
infixl 9 !!
(!!) :: [a] -> Integer -> a
_        !! n | n < 0 = traceError negativeIndexError
[]       !! _ = traceError indexTooLargeError
(x : xs) !! i = if Builtins.equalsInteger i 0
    then x
    else xs !! Builtins.subtractInteger i 1


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

{-# INLINABLE nub #-}
-- | Plutus Tx version of 'Data.List.nub'.
nub :: (Eq a) => [a] -> [a]
nub =  nubBy (==)

{-# INLINABLE elemBy #-}
-- | Plutus Tx version of 'Data.List.elemBy'.
elemBy :: (a -> a -> Bool) -> a -> [a] -> Bool
elemBy _  _ []     =  False
elemBy eq y (x:xs) =  x `eq` y || elemBy eq y xs

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
zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith f = go
  where
    go [] _          = []
    go _ []          = []
    go (x:xs) (y:ys) = f x y : go xs ys

{-# INLINABLE dropWhile #-}
-- | Plutus Tx version of 'Data.List.dropWhile'.
dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile _ []          =  []
dropWhile p xs@(x:xs')
    | p x       =  dropWhile p xs'
    | otherwise =  xs

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
