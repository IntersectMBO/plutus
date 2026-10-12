{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:no-conservative-optimisation #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:no-preserve-logging #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:remove-trace #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:target-version=1.2.0 #-}

module BuiltinCasing.TargetVersion.V120 (decodeAB, decodeMaybe) where

import BuiltinCasing.TargetVersion.Lib (AB (..))
import PlutusTx.Builtins (BuiltinData)
import PlutusTx.Code (CompiledCode)
import PlutusTx.IsData (unsafeFromBuiltinData)
import PlutusTx.TH (compile)

decodeAB :: CompiledCode (BuiltinData -> Integer)
decodeAB =
  $$( compile
        [||
        \d -> case unsafeFromBuiltinData d of
          A -> 0
          B -> 1
        ||]
    )

decodeMaybe :: CompiledCode (BuiltinData -> Integer)
decodeMaybe =
  $$( compile
        [||
        \d -> case unsafeFromBuiltinData d of
          Just n -> n
          Nothing -> 0
        ||]
    )
