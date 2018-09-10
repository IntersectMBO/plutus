{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
-- remove when we can use addCorePlugin
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin #-}

-- | Most tests for this functionality are in the plugin package, this is mainly just checking that the wiring machinery
-- works.
module Main (main) where

import           Language.Plutus.TH

import           Language.PlutusCore

import           TestTH

import           Test.Tasty
import           Test.Tasty.Golden

import qualified Data.ByteString.Lazy as BSL
import           Data.Text.Encoding   (encodeUtf8)

main :: IO ()
main = defaultMain tests

golden :: String -> PlcCode -> TestTree
golden name value = (goldenVsString name ("test/" ++ name ++ ".plc.golden") . pure . BSL.fromStrict . encodeUtf8 . debugText . getAst) value


tests :: TestTree
tests = testGroup "Plutus TH frontend" [
    golden "simple" simple
    , golden "power" powerPlc
  ]

simple :: PlcCode
simple = $$(plutusT [|| \(x::Bool) -> if x then (1::Int) else (2::Int) ||])

-- similar to the power example for Feldspar - should be completely unrolled at compile time
powerPlc :: PlcCode
powerPlc = $$(plutusT [|| $$(power (4::Int)) ||])
