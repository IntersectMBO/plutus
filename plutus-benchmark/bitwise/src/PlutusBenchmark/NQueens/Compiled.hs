{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}

module PlutusBenchmark.NQueens.Compiled
  ( nqueensCompiled
  , dimAsData
  ) where

import Plinth.Plugin ()
import PlutusBenchmark.NQueens (nqueens)
import PlutusTx.Code (CompiledCode)
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Prelude
import PlutusTx.TH (compile)

nqueensCompiled :: CompiledCode (BuiltinData -> [(Integer, Integer)])
nqueensCompiled = $$(compile [||\dim -> nqueens (unsafeFromBuiltinData dim)||])

dimAsData :: CompiledCode BuiltinData
dimAsData = liftCodeDef (toBuiltinData (8 :: Integer))
