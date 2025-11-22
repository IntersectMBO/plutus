{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=SumsOfProducts #-}

module PlutusBenchmark.SOP.List.SOP where

import PlutusTx
import PlutusTx.Prelude
import Prelude ()

data SOPList a = SOPCons a (SOPList a) | SOPNil

sumSOPList' :: SOPList Integer -> Integer
sumSOPList' (SOPCons x rest) = sumSOPList' rest + x
sumSOPList' SOPNil           = 0

replicateSOPList' :: Integer -> a -> SOPList a
replicateSOPList' n x =
  if n <= 0
  then SOPNil
  else SOPCons x (replicateSOPList' (n-1) x)

sumSOPList :: CompiledCode (SOPList Integer -> Integer)
sumSOPList = $$(compile [||sumSOPList'||])

replicateSOPList :: CompiledCode (Integer -> Integer -> SOPList Integer)
replicateSOPList = $$(compile [||replicateSOPList'||])
