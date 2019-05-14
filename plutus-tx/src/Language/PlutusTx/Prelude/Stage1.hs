{-# LANGUAGE TemplateHaskell #-}
-- Need `>` and `==` for doctests, annoyingly
{-# OPTIONS_GHC -Wno-unused-imports #-}
-- | The prelude functions are split into dependent modules so that we obey the TH staging restriction when
-- reusing functions.
module Language.PlutusTx.Prelude.Stage1 where

import           Prelude                    (Bool (..), Integer, Maybe(..), (>), (==))

import           Language.PlutusTx.Prelude.Stage0

import           Language.Haskell.TH

-- | 'length' @xs@ is the number of elements in @xs@.
--
--   >>> $$([|| $$(length) [1, 2, 3, 4] ||])
--   4
--
length :: Q (TExp ([a] -> Integer))
length = [|| $$(foldr) (\_ acc -> $$plus acc 1) 0 ||]

-- | PlutusTx version of 'Data.List.all'.
--
--   >>> $$([|| $$(all) (\i -> i > 5) [6, 8, 12] ||])
--   True
--
all :: Q (TExp ((a -> Bool) -> [a] -> Bool))
all = [|| \pred -> $$(foldr) (\a acc -> $$(and) acc (pred a)) True ||]

-- | PlutusTx version of 'Data.List.any'.
--
--   >>> $$([|| $$(any) (\i -> i > 5) [6, 2, 1] ||])
--   True
--
any :: Q (TExp ((a -> Bool) -> [a] -> Bool))
any = [|| \pred -> $$(foldr) (\a acc -> $$(or) acc (pred a)) False ||]

-- | PlutusTx version of 'Data.List.(++)'.
--
--   >>> $$([|| $$(append) [0, 1, 2] [1, 2, 3, 4] ||])
--   [0,1,2,1,2,3,4]
--
append :: Q (TExp ([a] -> [a] -> [a]))
append = [|| \l r -> $$(foldr) (\x xs -> x:xs) r l ||]

-- | PlutusTx version of 'Data.List.filter'.
--
--   >>> $$([|| $$(filter) (> 1) [1, 2, 3, 4] ||])
--   [2,3,4]
--
filter :: Q (TExp ((a -> Bool) -> [a] -> [a] ))
filter = [|| \pred -> $$(foldr) (\e xs -> if pred e then e:xs else xs) [] ||]

-- | PlutusTx version of 'Data.Maybe.mapMaybe'.
--
--   >>> $$([|| $$(mapMaybe) (\i -> if i == 2 then Just '2' else Nothing) [1, 2, 3, 4] ||])
--   "2"
--
mapMaybe :: Q (TExp ((a -> Maybe b) -> [a] -> [b]))
mapMaybe = [|| \pred -> $$(foldr) (\e xs -> case pred e of { Just e' -> e':xs; Nothing -> xs}) [] ||]
