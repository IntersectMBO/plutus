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

import Data.ByteString.Short qualified as SBS
import Data.Set qualified as Set
import Example.Ual.Recursive.FormalSpec (annotations)
import Example.Ual.Recursive.OnChain
import PlutusLedgerApi.V3 (serialiseCompiledCode)
import PlutusTx qualified
import PlutusTx.Assurance
import PlutusTx.Blueprint
import PlutusTx.Prelude (BuiltinData, BuiltinUnit)
import System.Environment (getArgs)

treeCode :: PlutusTx.CompiledCode (BuiltinData -> BuiltinData -> BuiltinUnit)
treeCode = $$(PlutusTx.compile [||treeValidator||])
mirrorCode :: PlutusTx.CompiledCode (BuiltinData -> BuiltinData)
mirrorCode = $$(PlutusTx.compile [||mirrorData||])

blueprint :: ContractBlueprint
blueprint =
  MkContractBlueprint
    { contractId = Just "recursive-data-spec"
    , contractPreamble = MkPreamble "Recursive tree" Nothing "1.0.0" PlutusV3 Nothing
    , contractValidators =
        Set.singleton
          mkValidatorBlueprint
            { validatorId = Just "treeValidator"
            , validatorTitle = "Tree validator"
            , validatorParameters =
                [MkParameterBlueprint Nothing Nothing (Set.singleton Spend) (definitionRef @Tree)]
            , validatorRedeemer =
                MkArgumentBlueprint Nothing Nothing (Set.singleton Spend) (definitionRef @BuiltinData)
            , validatorCompiled =
                Just (compiledValidator PlutusV3 (SBS.fromShort (serialiseCompiledCode treeCode)))
            }
    , contractDefinitions = deriveRecursiveDefinitions @'[Tree, BuiltinData]
    }

main :: IO ()
main = do
  args <- getArgs
  environment <- case args of
    [path] -> pure path
    _ -> fail "usage: example-ual-recursive ENVIRONMENT.json"
  let preamble =
        MkAssurancePreamble
          "Recursive Data with detached specification"
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
    [compiledFunction "mirrorData" mirrorCode]
