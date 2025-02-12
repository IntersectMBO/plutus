{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

-- These flags turn off most optimizations
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}

module MyScript where

import PlutusTx.Code
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.TH (compile)

len :: [Integer] -> Integer
len = \case
  [] -> 0
  (_ : xs) -> 1 PlutusTx.+ len xs

compiledLen :: CompiledCode ([Integer] -> Integer)
compiledLen = $$(compile [||len||])
