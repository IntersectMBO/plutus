{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Spec.Envelope where

import PlutusLedgerApi.Envelope (writeCodeEnvelope)
import PlutusTx qualified
import PlutusTx.Prelude qualified as P
import System.FilePath ((</>))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsFile)

tests :: TestTree
tests = testGroup "Envelope" [testTrivialEnvelope]

testTrivialEnvelope :: TestTree
testTrivialEnvelope =
  goldenVsFile "writeCodeEnvelope produces expected JSON" golden actual $
    writeCodeEnvelope
      "A trivial function that computes 2 + 2"
      $$(PlutusTx.compile [||(2 :: Integer) P.+ 2||])
      actual
  where
    basePath :: FilePath
    basePath = "test-plugin/golden"

    actual :: FilePath
    actual = basePath </> "envelope.actual.json"

    golden :: FilePath
    golden = basePath </> "envelope.json"
