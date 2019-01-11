{-# LANGUAGE TemplateHaskell #-}
-- Need `>` for doctests, annoyingly
{-# OPTIONS_GHC -Wno-unused-imports #-}
-- | The prelude functions are split into dependent modules so that we obey the TH staging restriction when
-- reusing functions.
module Language.PlutusTx.Prelude.Stage1 where

import           Prelude                    (Bool (..), Int, (+), (>))

import           Language.PlutusTx.Prelude.Stage0

import           Language.Haskell.TH

-- | 'length' @xs@ is the number of elements in @xs@.
--
--   >>> $$([|| $$(length) [1, 2, 3, 4] ||])
--   4
--
length :: Q (TExp ([a] -> Int))
length = [|| $$(foldr) (\_ acc -> acc+1) 0 ||]

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
