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
ed25519Compiled = $$(compile [||
  let msg = "hello world"
      signature = "\NUL\147!x\173\167\209z`\t\243|\195$X$\233\166\234\NUL\134\152l\DC4\243\&4\217\NAK\152\180{$M\227R\214\218%\241\157\ENQ\SO\ENQ\t\152\140\171\240\200f\184\133\203\227z\163\NUL\185\155Y\139\178\249\STX"
      pk = "(:\255\251\129\&7-^w\253\145\vh\ESC\171r\189\223/\213Qzb\249\175$z\211q\195\DC1\198"
    in checkValid signature msg pk
 ||])

nqueensCompiled :: CompiledCode [(Integer, Integer)]
nqueensCompiled = $$(compile [||nqueens 8||])
