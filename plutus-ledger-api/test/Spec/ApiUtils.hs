{-# LANGUAGE OverloadedStrings #-}

module Spec.ApiUtils (tests) where

import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Short qualified as SBS
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Text.IO qualified as Text
import PlutusLedgerApi.Common
import System.FilePath (joinPath, (</>))
import Test.Tasty
import Test.Tasty.HUnit

path :: [FilePath]
path = ["test", "Spec", "CompiledScripts"]

-- Script bytes and hashes used for the following tests are obtained from real mainnet scripts.
tests :: TestTree
tests = testGroup "Plutus Core language versions"
  [ testCase "ScriptHash correct" $ do
      let scriptV1Path = joinPath path </> "CompiledValidatorV1.hex"
          scriptV2Path = joinPath path </> "CompiledValidatorV2.hex"

      compiledV1ScriptInHex <- Text.readFile scriptV1Path
      compiledV2ScriptInHex <- Text.readFile scriptV2Path

      assertBool "Plutus Language V1 ScriptHash match expected" $
        toHex (hashScriptWithPrefix 0x1 (SBS.toShort $ fromHex compiledV1ScriptInHex))
          == "232c10966ce4d8e67c2eae17bb57c2cf4854a57509a752fbb3c02bd1"

      assertBool "Plutus Language V2 ScriptHash match expected" $
        toHex (hashScriptWithPrefix 0x2 (SBS.toShort $ fromHex compiledV2ScriptInHex))
          == "fa6a58bbe2d0ff05534431c8e2f0ef2cbdc1602a8456e4b13c8f3077"
  ]
  where
    fromHex script =
      case (Base16.decode . Text.encodeUtf8 . Text.strip $ script) of
        Left _  -> Prelude.error "Failed to decode hex"
        Right x -> x
    toHex = Text.decodeUtf8 . Base16.encode
