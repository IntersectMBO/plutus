-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Criterion.Main (bench, defaultMain)
import PlutusBenchmark.Common (benchProgramCek, mkMostRecentEvalCtx)
import PlutusBenchmark.Ed25519.Compiled (checkValidCompiled, msgAsData, pkAsData, signatureAsData)
import PlutusBenchmark.NQueens.Compiled (dimAsData, nqueensCompiled)
import PlutusTx.Code (getPlcNoAnn, unsafeApplyCode)

main :: IO ()
main =
  defaultMain
    [ bench "Ed25519" . benchProgramCek mkMostRecentEvalCtx . getPlcNoAnn $
        checkValidCompiled `unsafeApplyCode` signatureAsData `unsafeApplyCode` msgAsData `unsafeApplyCode` pkAsData
    , bench "8-queens" . benchProgramCek mkMostRecentEvalCtx . getPlcNoAnn $
        nqueensCompiled `unsafeApplyCode` dimAsData
    ]
