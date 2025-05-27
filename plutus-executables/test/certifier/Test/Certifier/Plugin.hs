{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:certify=ScriptContextCert #-}

module Test.Certifier.Plugin where

import PlutusTx.Test.Util.Compiled (compiledCodeToCertPath)

import Test.Certifier.Executable (runAgda)

import PlutusBenchmark.V2.Data.ScriptContexts qualified as Data (forwardWithStakeTrick)

import PlutusTx qualified

import Data.Maybe (fromJust)
import System.Directory (removeDirectoryRecursive)
import System.Exit

import Test.Tasty
import Test.Tasty.HUnit

mkCertTest :: String -> PlutusTx.CompiledCode a -> TestTree
mkCertTest name code = testCase name $ do
  let cPath = fromJust $ compiledCodeToCertPath code
  (resECode, resText) <- runAgda cPath
  -- removeDirectoryRecursive cPath
  putStrLn cPath
  assertBool
    (name <> " creates an invalid certificate:" <> resText)
    (resECode == ExitSuccess)

pluginTests :: TestTree
pluginTests =
  testGroup "Certifier with plugin tests" $
    [ mkCertTest "TESTING Data.forwardWithStakeTrick" $$(PlutusTx.compile [|| Data.forwardWithStakeTrick ||])
    -- Add more tests here as needed
    ]
