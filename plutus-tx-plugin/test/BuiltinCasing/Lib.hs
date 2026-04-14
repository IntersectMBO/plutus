{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}

{-# HLINT ignore #-}

module BuiltinCasing.Lib (failsToCompile) where

import PlutusTx
import PlutusTx.Builtins.Internal (unitval)
import PlutusTx.Data.List (caseList')
import PlutusTx.Prelude

failsToCompile :: BuiltinData -> BuiltinUnit
failsToCompile bd =
  case toBuiltinData (firstOf items) of
    _ -> case toBuiltinData (firstOf items) of
      _ -> unitval
  where
    items = unsafeFromBuiltinData bd
    firstOf = caseList' Nothing (\(h :: BuiltinData) _t -> Just h)
