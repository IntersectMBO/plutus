{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Language.PlutusTx.List (null, map, foldr, foldl, length, all, any, filter, (++)) where

import           Language.PlutusTx.Bool
import qualified Language.PlutusTx.Builtins as Builtins
import           Prelude                    hiding (all, any, filter, foldl, foldr, length, map, null, (&&), (++), (||))

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
-- eta-expanded to avoid the value restriction
length as = foldr (\_ acc -> Builtins.addInteger acc 1) 0 as

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

{-# INLINABLE (++) #-}
-- | PlutusTx version of 'Data.List.(++)'.
--
--   >>> [0, 1, 2] ++ [1, 2, 3, 4]
--   [0,1,2,1,2,3,4]
--
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
