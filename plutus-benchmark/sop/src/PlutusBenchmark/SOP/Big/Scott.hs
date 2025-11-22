{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=ScottEncoding #-}

module PlutusBenchmark.SOP.Big.Scott where

import PlutusTx
import PlutusTx.Prelude
import Prelude ()

data ScottBig
  = ScottBigA Integer Integer Integer Integer Integer ScottBig
  | ScottBigB Integer Integer Integer Integer Integer ScottBig
  | ScottBigC Integer Integer Integer Integer Integer ScottBig
  | ScottBigD Integer Integer Integer Integer Integer ScottBig
  | ScottBigE Integer Integer Integer Integer Integer ScottBig
  | ScottBigNil

mkScottBigFull' :: Integer -> Integer -> ScottBig
mkScottBigFull' 0 _ = ScottBigNil
mkScottBigFull' n x =
  ScottBigA x x x x x
   (ScottBigB x x x x x
    (ScottBigC x x x x x
     (ScottBigD x x x x x
      (ScottBigE x x x x x (mkScottBigFull' (n - 1) x)))))

sumScottBig' :: ScottBig -> Integer
sumScottBig' (ScottBigA a b c d e rest) =
  a + b + c + d + e + (sumScottBig' rest)
sumScottBig' (ScottBigB a b c d e rest) =
  a + b + c + d + e + (sumScottBig' rest)
sumScottBig' (ScottBigC a b c d e rest) =
  a + b + c + d + e + (sumScottBig' rest)
sumScottBig' (ScottBigD a b c d e rest) =
  a + b + c + d + e + (sumScottBig' rest)
sumScottBig' (ScottBigE a b c d e rest) =
  a + b + c + d + e + (sumScottBig' rest)
sumScottBig' ScottBigNil = 0

mkScottBigFull :: CompiledCode (Integer -> Integer -> ScottBig)
mkScottBigFull = $$(compile [||mkScottBigFull'||])

sumScottBig :: CompiledCode (ScottBig -> Integer)
sumScottBig = $$(compile [||sumScottBig'||])
