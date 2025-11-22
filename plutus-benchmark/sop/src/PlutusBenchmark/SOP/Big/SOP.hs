{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=SumsOfProducts #-}

module PlutusBenchmark.SOP.Big.SOP where

import PlutusTx
import PlutusTx.Prelude
import Prelude ()

data SOPBig
  = SOPBigA Integer Integer Integer Integer Integer SOPBig
  | SOPBigB Integer Integer Integer Integer Integer SOPBig
  | SOPBigC Integer Integer Integer Integer Integer SOPBig
  | SOPBigD Integer Integer Integer Integer Integer SOPBig
  | SOPBigE Integer Integer Integer Integer Integer SOPBig
  | SOPBigNil

mkSOPBigFull' :: Integer -> Integer -> SOPBig
mkSOPBigFull' 0 _ = SOPBigNil
mkSOPBigFull' n x =
  SOPBigA x x x x x
   (SOPBigB x x x x x
    (SOPBigC x x x x x
     (SOPBigD x x x x x
      (SOPBigE x x x x x (mkSOPBigFull' (n - 1) x)))))

sumSOPBig' :: SOPBig -> Integer
sumSOPBig' (SOPBigA a b c d e rest) =
  a + b + c + d + e + (sumSOPBig' rest)
sumSOPBig' (SOPBigB a b c d e rest) =
  a + b + c + d + e + (sumSOPBig' rest)
sumSOPBig' (SOPBigC a b c d e rest) =
  a + b + c + d + e + (sumSOPBig' rest)
sumSOPBig' (SOPBigD a b c d e rest) =
  a + b + c + d + e + (sumSOPBig' rest)
sumSOPBig' (SOPBigE a b c d e rest) =
  a + b + c + d + e + (sumSOPBig' rest)
sumSOPBig' SOPBigNil = 0

mkSOPBigFull :: CompiledCode (Integer -> Integer -> SOPBig)
mkSOPBigFull = $$(compile [||mkSOPBigFull'||])

sumSOPBig :: CompiledCode (SOPBig -> Integer)
sumSOPBig = $$(compile [||sumSOPBig'||])
