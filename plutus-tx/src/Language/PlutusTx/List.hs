{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Language.PlutusTx.List (null, map, foldr, foldl, length, all, any, elem, filter, listToMaybe, uniqueElement, findIndices, findIndex, find, reverse, zip, (++), (!!)) where

import           Language.PlutusTx.Bool
import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Eq
import           Prelude                    hiding (Eq (..), all, any, elem, filter, foldl, foldr, length, map, null,
                                             reverse, zip, (!!), (&&), (++), (||))

{-# ANN module ("HLint: ignore"::String) #-}

{-# INLINABLE null #-}
-- | PlutusTx version of 'Data.List.null'.
--
--   >>> null [1]
--   False
--   >>> null []
--   True
--
null :: [a] -> Bool
null l = case l of
    [] -> True
    _  -> False

{-# INLINABLE map #-}
-- | PlutusTx version of 'Data.List.map'.
--
--   >>> map (\i -> i + 1) [1, 2, 3]
--   [2,3,4]
--
map :: (a -> b) -> [a] -> [b]
map f l = case l of
    []   -> []
    x:xs -> f x : map f xs

{-# INLINABLE foldr #-}
-- | PlutusTx version of 'Data.List.foldr'.
--
--   >>> foldr (\i s -> s + i) 0 [1, 2, 3, 4]
--   10
--
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f acc l = case l of
    []   -> acc
    x:xs -> f x (foldr f acc xs)

{-# INLINABLE foldl #-}
-- | PlutusTx version of 'Data.List.foldl'.
--
--   >>> foldl (\s i -> s + i) 0 [1, 2, 3, 4]
--   10
--
foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f acc l = case l of
    []   -> acc
    x:xs -> foldl f (f acc x) xs

{-# INLINABLE length #-}
-- | 'length' @xs@ is the number of elements in @xs@.
--
--   >>> length [1, 2, 3, 4]
--   4
--
length :: [a] -> Integer
length = foldr (\_ acc -> Builtins.addInteger acc 1) 0

{-# INLINABLE all #-}
-- | PlutusTx version of 'Data.List.all'.
--
--   >>> all (\i -> i > 5) [6, 8, 12]
--   True
--
all :: (a -> Bool) -> [a] -> Bool
all p = foldr (\a acc -> acc && p a) True

{-# INLINABLE any #-}
-- | PlutusTx version of 'Data.List.any'.
--
--   >>> any (\i -> i > 5) [6, 2, 1]
--   True
--
any :: (a -> Bool) -> [a] -> Bool
any p = foldr (\a acc -> acc || p a) False

{-# INLINABLE elem #-}
-- | PlutusTx version of 'Data.List.elem'.
elem :: Eq a => a -> [a] -> Bool
elem needle haystack = case haystack of
    []   -> False
    x:xs -> if x == needle then True else needle `elem` xs

{-# INLINABLE (++) #-}
-- | PlutusTx version of 'Data.List.(++)'.
--
--   >>> [0, 1, 2] ++ [1, 2, 3, 4]
--   [0,1,2,1,2,3,4]
--
infixr 5 ++
(++) :: [a] -> [a] -> [a]
(++) l r = foldr (:) r l

{-# INLINABLE filter #-}
-- | PlutusTx version of 'Data.List.filter'.
--
--   >>> filter (> 1) [1, 2, 3, 4]
--   [2,3,4]
--
filter :: (a -> Bool) -> [a] -> [a]
filter p = foldr (\e xs -> if p e then e:xs else xs) []

{-# INLINABLE listToMaybe #-}
-- | PlutusTx version of 'Data.List.listToMaybe'.
listToMaybe :: [a] -> Maybe a
listToMaybe []    = Nothing
listToMaybe (x:_) = Just x

{-# INLINABLE uniqueElement #-}
-- | Return the element in the list, if there is precisely one.
uniqueElement :: [a] -> Maybe a
uniqueElement [x] = Just x
uniqueElement _   = Nothing

{-# INLINABLE findIndices #-}
-- | PlutusTx version of 'Data.List.findIndices'.
findIndices :: (a -> Bool) -> [a] -> [Integer]
findIndices p = go 0
    where
        go i l = case l of
            []     -> []
            (x:xs) -> let indices = go (Builtins.addInteger i 1) xs in if p x then i:indices else indices

{-# INLINABLE findIndex #-}
-- | PlutusTx version of 'Data.List.findIndex'.
findIndex :: (a -> Bool) -> [a] -> Maybe Integer
findIndex p l = listToMaybe (findIndices p l)

{-# INLINABLE find #-}
-- | PlutusTx version of 'Data.List.find'.
find :: (a -> Bool) -> [a] -> Maybe a
find p = go
    where
        go l = case l of
            []     -> Nothing
            (x:xs) -> if p x then Just x else go xs

{-# INLINABLE (!!) #-}
-- | PlutusTx version of 'GHC.List.(!!)'.
--
--   >>> [10, 11, 12] !! 2
--   12
--
infixl 9 !!
(!!) :: [a] -> Integer -> a
[]       !! _ = Builtins.error ()
(x : xs) !! i = if Builtins.equalsInteger i 0
    then x
    else xs !! Builtins.subtractInteger i 1


{-# INLINABLE reverse #-}
-- | 'reverse' @xs@ returns the elements of @xs@ in reverse order.
-- @xs@ must be finite.
reverse :: [a] -> [a]
reverse l = rev l []
  where
    rev []      a = a
    rev (x:xs) a  = rev xs (x:a)


{-# INLINABLE zip #-}
zip :: [a] -> [b] -> [(a,b)]
zip []     _bs    = []
zip _as    []     = []
zip (a:as) (b:bs) = (a,b) : zip as bs
