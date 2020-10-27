{-# LANGUAGE NoImplicitPrelude #-}

module Plutus.Benchmark.Knights.Utils where

import           Language.PlutusTx.Prelude

{-# INLINABLE take' #-}
take' :: Integer -> [a] -> [a]
take' _ []     = []
take' n (a:as) = if n<=0 then [] else a:(take' (n-1) as)
