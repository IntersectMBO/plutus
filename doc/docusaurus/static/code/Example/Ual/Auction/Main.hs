{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-full-laziness -fno-ignore-interface-pragmas -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr -fno-specialise -fno-strictness #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:target-version=1.1.0 #-}

module Main where

import AuctionValidator (auctionValidatorScript)
import Data.ByteString.Short qualified as SBS
import Data.Set qualified as Set
import Example.Ual.Auction.FormalSpec (annotations)
import Example.Ual.Auction.OnChain
import PlutusLedgerApi.V3 (serialiseCompiledCode)
import PlutusTx qualified
import PlutusTx.Assurance
import PlutusTx.Blueprint
import PlutusTx.Prelude (BuiltinData, BuiltinUnit)
import System.Environment (getArgs)

auctionCode :: PlutusTx.CompiledCode (BuiltinData -> BuiltinUnit)
auctionCode = auctionValidatorScript params
outbidsCode :: PlutusTx.CompiledCode (Integer -> Integer -> Bool)
outbidsCode = $$(PlutusTx.compile [||outbids||])

blueprint :: ContractBlueprint
blueprint =
  MkContractBlueprint
    { contractId = Just "auction-detached-spec"
    , contractPreamble = MkPreamble "Auction" Nothing "1.0.0" PlutusV3 Nothing
    , contractValidators =
        Set.singleton
          mkValidatorBlueprint
            { validatorId = Just "auction"
            , validatorTitle = "Auction"
            , validatorRedeemer =
                MkArgumentBlueprint Nothing Nothing (Set.singleton Spend) (definitionRef @BuiltinData)
            , validatorCompiled =
                Just (compiledValidator PlutusV3 (SBS.fromShort (serialiseCompiledCode auctionCode)))
            }
    , contractDefinitions = deriveDefinitions @'[BuiltinData]
    }

main :: IO ()
main = do
  args <- getArgs
  environment <- case args of
    [path] -> pure path
    _ -> fail "usage: example-ual-auction ENVIRONMENT.json"
  let preamble =
        MkAssurancePreamble
          "Auction with detached specification"
          Nothing
          (Just "1.0.0")
          ["Plutus contributors"]
          "2026-10-06"
          Nothing
  writeInterfaceBundleWithFunctions
    environment
    preamble
    ""
    [annotations]
    blueprint
    [compiledFunction "outbids" outbidsCode]
