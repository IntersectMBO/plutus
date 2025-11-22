{-# LANGUAGE NoImplicitPrelude #-}

module PlutusBenchmark.NoFib.Knights.Utils where

import PlutusTx.Prelude

take' :: Integer -> [a] -> [a]
take' _ [] = []
take' n (a : as) = if n <= 0 then [] else a : (take' (n - 1) as)
{-# INLINEABLE take' #-}
