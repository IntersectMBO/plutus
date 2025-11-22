{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=ScottEncoding #-}

module PlutusBenchmark.SOP.List.Scott where

import PlutusTx
import PlutusTx.Prelude
import Prelude ()

data ScottList a = ScottCons a (ScottList a) | ScottNil

sumScottList' :: ScottList Integer -> Integer
sumScottList' (ScottCons x rest) = sumScottList' rest + x
sumScottList' ScottNil           = 0

replicateScottList' :: Integer -> a -> ScottList a
replicateScottList' n x =
  if n <= 0
  then ScottNil
  else ScottCons x (replicateScottList' (n-1) x)

sumScottList :: CompiledCode (ScottList Integer -> Integer)
sumScottList = $$(compile [||sumScottList'||])

replicateScottList :: CompiledCode (Integer -> Integer -> ScottList Integer)
replicateScottList = $$(compile [||replicateScottList'||])
