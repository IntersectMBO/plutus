{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}

module PlutusBenchmark.NQueens.Compiled (
  nqueensCompiled,
  dimAsData
  ) where

import PlutusBenchmark.NQueens (nqueens)
import PlutusTx.Code (CompiledCode)
import PlutusTx.IsData (toBuiltinData, unsafeFromBuiltinData)
import PlutusTx.Plugin ()
import PlutusTx.Prelude
import PlutusTx.TH (compile)

nqueensCompiled :: CompiledCode (BuiltinData -> [(Integer, Integer)])
nqueensCompiled = $$(compile [|| \dim -> nqueens (unsafeFromBuiltinData dim) ||])

dimAsData :: CompiledCode BuiltinData
dimAsData = $$(compile [|| toBuiltinData (8 :: Integer) ||])
