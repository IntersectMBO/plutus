{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import Criterion.Main (bench, defaultMain)
import PlutusBenchmark.Common (benchProgramCek, mkMostRecentEvalCtx)
import PlutusBenchmark.NQueens (nqueens)
import PlutusTx.Code (CompiledCode, getPlcNoAnn)
import PlutusTx.Plugin ()
import PlutusTx.TH (compile)

main :: IO ()
main = defaultMain [
  bench "8-queens" . benchProgramCek mkMostRecentEvalCtx . getPlcNoAnn $ nqueensCompiled
  ]

-- Helpers

nqueensCompiled :: CompiledCode [(Integer, Integer)]
nqueensCompiled = $$(compile [|| nqueens 8 ||])

