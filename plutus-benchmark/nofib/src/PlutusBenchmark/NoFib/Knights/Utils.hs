{-# LANGUAGE NoImplicitPrelude #-}

module PlutusBenchmark.NoFib.Knights.Utils where

import PlutusTx.Prelude hiding ((*), (+), (-), (/=), (<), (<=), (==), (>), (>=))
import Prelude qualified as Haskell

{-# INLINABLE take' #-}
take' :: Integer -> [a] -> [a]
take' _ []     = []
take' n (a:as) = if n Haskell.<= 0 then [] else a:(take' (n Haskell.- 1) as)
