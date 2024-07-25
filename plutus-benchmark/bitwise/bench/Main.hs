-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Main (main) where

import Criterion.Main (bench, defaultMain)
import PlutusBenchmark.Common (benchProgramCek, mkMostRecentEvalCtx)
import PlutusBenchmark.NQueens (nqueens)
import PlutusTx.Code (CompiledCode, getPlcNoAnn)
import PlutusTx.Plugin ()
import PlutusBenchmark.Ed25519 (checkValid)
import PlutusTx.Code (CompiledCode, getPlcNoAnn)
import PlutusTx.TH (compile)

main :: IO ()
main = defaultMain [
  bench "8-queens" . benchProgramCek mkMostRecentEvalCtx . getPlcNoAnn $ nqueensCompiled,
  bench "Ed25519" . benchProgramCek mkMostRecentEvalCtx . getPlcNoAnn $ ed25519Compiled
  ]

-- Helpers

nqueensCompiled :: CompiledCode [(Integer, Integer)]
nqueensCompiled = $$(compile [|| nqueens 8 ||])

ed25519Compiled :: CompiledCode Bool
ed25519Compiled = $$(compile [|| checkValid "x\\SUB`\\EOT\\209\\145$h\\209\\207\\193\\b\\149\\253\\249%\\231\\b\\DC1s\\212\\191l/\\v)\\235\\208\\200tW\\155\\202\\163\\&8Z\\n\\rzojc\\\\\\189\\&3\\230\\139\\171\\GS\\162\\129\\\\|=\\253\\ACK.\\137&^\\SOH\\ETX\\216\\v"
                                            "hello world"
                                            "V\\244\\f8\\223\\229\\&2\\189Z@\\137F\\168\\221\\245\\&3\\137W\\EOT\\229\\223T)O\\219\\SI\\242\\153\\CAN\\210Nw" ||])
