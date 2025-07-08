-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Criterion.Main (defaultMain)
import PlutusBenchmark.Common (benchProgramCek, mkMostRecentEvalCtx)
import PlutusBenchmark.Ed25519.Compiled (checkValidCompiled, msgAsData, pkAsData, signatureAsData)
import PlutusBenchmark.NQueens.Compiled (dimAsData, nqueensCompiled)
import PlutusTx.Code (getPlcNoAnn, unsafeApplyCode)

main :: IO ()
main = defaultMain [
  benchProgramCek "Ed25519" mkMostRecentEvalCtx . getPlcNoAnn $
    checkValidCompiled `unsafeApplyCode` signatureAsData `unsafeApplyCode` msgAsData `unsafeApplyCode` pkAsData,
  benchProgramCek "8-queens" mkMostRecentEvalCtx . getPlcNoAnn $
    nqueensCompiled `unsafeApplyCode` dimAsData
  ]
