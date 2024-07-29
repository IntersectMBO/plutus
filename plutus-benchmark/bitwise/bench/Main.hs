-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Main (main) where

import Criterion.Main (bench, defaultMain)
import PlutusBenchmark.Common (benchProgramCek, mkMostRecentEvalCtx)
import PlutusBenchmark.NQueens (nqueens)
import PlutusTx.Builtins (BuiltinByteString, BuiltinData)
import PlutusTx.Code (CompiledCode, getPlcNoAnn, unsafeApplyCode)
import PlutusTx.IsData (toBuiltinData, unsafeFromBuiltinData)
import PlutusTx.TH (compile)

main :: IO ()
main = defaultMain [
  bench "Ed25519" . benchProgramCek mkMostRecentEvalCtx . getPlcNoAnn $
    checkValidCompiled `unsafeApplyCode` signatureAsData `unsafeApplyCode` msgAsData `unsafeApplyCode` pkAsData,
  bench "8-queens" . benchProgramCek mkMostRecentEvalCtx . getPlcNoAnn $
    nqueensCompiled `unsafeApplyCode` dimAsData
  ]

-- Helpers

checkValidCompiled :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> Bool)
checkValidCompiled = $$(compile [|| \signature msg pk -> checkValid (unsafeFromBuiltinData signature)
                                                                    (unsafeFromBuiltinData msg)
                                                                    (unsafeFromBuiltinData pk) ||])

msgAsData :: CompiledCode BuiltinData
msgAsData = $$(compile [|| toBuiltinData ("hello world" :: BuiltinByteString) ||])

signatureAsData :: CompiledCode BuiltinData
signatureAsData =
  $$(compile [|| toBuiltinData ("\NUL\147!x\173\167\209z`\t\243|\195$X$\233\166\234\NUL\134\152l\DC4\243\&4\217\NAK\152\180{$M\227R\214\218%\241\157\ENQ\SO\ENQ\t\152\140\171\240\200f\184\133\203\227z\163\NUL\185\155Y\139\178\249\STX" :: BuiltinByteString) ||])

pkAsData :: CompiledCode BuiltinData
pkAsData =
  $$(compile [|| toBuiltinData ("(:\255\251\129\&7-^w\253\145\vh\ESC\171r\189\223/\213Qzb\249\175$z\211q\195\DC1\198" :: BuiltinByteString) ||])

nqueensCompiled :: CompiledCode (BuiltinData -> [(Integer, Integer)])
nqueensCompiled = $$(compile [|| \dim -> nqueens (unsafeFromBuiltinData dim) ||])

dimAsData :: CompiledCode BuiltinData
dimAsData = $$(compile [|| toBuiltinData (8 :: Integer) ||])
