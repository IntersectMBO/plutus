{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
-- remove when we can use addCorePlugin
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin #-}

-- | Most tests for this functionality are in the plugin package, this is mainly just checking that the wiring machinery
-- works.
module Main (main) where

import           Common

import           TestTH

import           Language.Plutus.TH

import qualified Language.PlutusCore.Pretty as PLC

import           Test.Tasty

main :: IO ()
main = defaultMain $ runTestNestedIn ["test"] tests

golden :: String -> PlcCode -> TestNested
golden name = nestedGoldenVsDoc name . PLC.prettyPlcClassicDebug . getAst

tests :: TestNested
tests = testGroup "plutus-th" <$> sequence [
    golden "simple" simple
    , golden "power" powerPlc
    , golden "and" andPlc
  ]

simple :: PlcCode
simple = $(plutus [| \(x::Bool) -> if x then (1::Int) else (2::Int) |])

-- similar to the power example for Feldspar - should be completely unrolled at compile time
powerPlc :: PlcCode
powerPlc = $(plutus [| $(power (4::Int)) |])

andPlc :: PlcCode
andPlc = $(plutus [| $(andTH) True False |])
