{-# LANGUAGE NoImplicitPrelude #-}

module Plutus.Benchmark.Knights.Utils where

import           Language.PlutusTx          as PlutusTx
import           Language.PlutusTx.Builtins as Tx
import           Language.PlutusTx.Prelude  as PLC

{-
{-# INLINABLE length' #-}
length' :: [a] -> Integer
length' []    = 0
length' (_:t) = 1 + length' t
-}

{-# INLINABLE take' #-}
take' :: Integer -> [a] -> [a]
take' _ []     = []
take' n (a:as) = a:(take' (n-1) as)

{-
{-# INLINABLE nth #-}
nth :: Integer -> [a] -> a
nth _ []     = Tx.error ()
nth 0 (a:_)  = a
nth n (_:as) = nth (n-1) as
-}
