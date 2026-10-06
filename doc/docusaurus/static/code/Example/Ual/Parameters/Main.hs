{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-full-laziness -fno-ignore-interface-pragmas -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr -fno-specialise -fno-strictness #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:target-version=1.0.0 #-}

module Main where

import Data.ByteString.Short qualified as SBS
import Data.Set qualified as Set
import PlutusLedgerApi.V2 (serialiseCompiledCode)
import PlutusTx qualified
import PlutusTx.Assurance
import PlutusTx.Blueprint
import PlutusTx.Prelude
import PlutusTx.Ual (ModuleUal)
import PlutusTx.Ual.TH (ualModule)
import System.Environment (getArgs)
import Prelude qualified as Haskell

-- Equal host integer types with different UPLC representations.
{-@ ONCHAIN [version: PlutusV2] [steps: 100, semantics: D]
    nativeParameter :: { Integer : asNative } -> BuiltinData -> BuiltinData -> BuiltinUnit
@-}
{-# INLINEABLE nativeParameter #-}
nativeParameter :: Integer -> BuiltinData -> BuiltinData -> BuiltinUnit
nativeParameter n _ _ = check (n == 7)

{-@ ONCHAIN [version: PlutusV2] [steps: 100, semantics: D]
    dataParameter :: { Integer : asData } -> BuiltinData -> BuiltinData -> BuiltinUnit
@-}
{-# INLINEABLE dataParameter #-}
dataParameter :: BuiltinData -> BuiltinData -> BuiltinData -> BuiltinUnit
dataParameter d _ _ = check ((unsafeFromBuiltinData d :: Integer) == 7)

{-@ PROPERTY [scope: nativeParameter] native_seven
    "The native parameter succeeds exactly for seven, for any runtime inputs."
  : ∀ (n : Integer) (r ctx : Data), isSuccessful (nativeParameter n r ctx) ↔ n = 7
@-}
{-@ PROPERTY [scope: dataParameter] data_seven
    "The Data parameter succeeds exactly for seven, for any runtime inputs."
  : ∀ (n : Integer) (r ctx : Data), isSuccessful (dataParameter n r ctx) ↔ n = 7
@-}

nativeCode :: PlutusTx.CompiledCode (Integer -> BuiltinData -> BuiltinData -> BuiltinUnit)
nativeCode = $$(PlutusTx.compile [||nativeParameter||])
dataCode :: PlutusTx.CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> BuiltinUnit)
dataCode = $$(PlutusTx.compile [||dataParameter||])

blueprint :: ContractBlueprint
blueprint =
  MkContractBlueprint
    { contractId = Just "parameter-encodings"
    , contractPreamble = MkPreamble "Parameter encodings" Nothing "1.0.0" PlutusV2 Nothing
    , contractValidators =
        Set.fromList
          [ mkValidatorBlueprint
              { validatorId = Just "nativeParameter"
              , validatorTitle = "Native parameter"
              , validatorParameters =
                  [MkParameterBlueprint Nothing Nothing (Set.singleton Mint) (SchemaBuiltInInteger emptySchemaInfo)]
              , validatorRedeemer =
                  MkArgumentBlueprint Nothing Nothing (Set.singleton Mint) (definitionRef @BuiltinData)
              , validatorCompiled =
                  Just (compiledValidator PlutusV2 (SBS.fromShort (serialiseCompiledCode nativeCode)))
              }
          , mkValidatorBlueprint
              { validatorId = Just "dataParameter"
              , validatorTitle = "Data parameter"
              , validatorParameters =
                  [MkParameterBlueprint Nothing Nothing (Set.singleton Mint) (definitionRef @Integer)]
              , validatorRedeemer =
                  MkArgumentBlueprint Nothing Nothing (Set.singleton Mint) (definitionRef @BuiltinData)
              , validatorCompiled =
                  Just (compiledValidator PlutusV2 (SBS.fromShort (serialiseCompiledCode dataCode)))
              }
          ]
    , contractDefinitions = deriveDefinitions @'[Integer, BuiltinData]
    }

$(Haskell.pure [])
annotations :: ModuleUal
annotations = $(ualModule)

main :: Haskell.IO ()
main = do
  args <- getArgs
  environment <- case args of
    [path] -> Haskell.pure path
    _ -> Haskell.fail "usage: example-ual-parameters ENVIRONMENT.json"
  let preamble =
        MkAssurancePreamble
          "Parameter encoding assurance"
          Nothing
          (Just "1.0.0")
          ["Plutus contributors"]
          "2026-09-30"
          Nothing
  writeInterfaceBundle environment preamble "" [annotations] blueprint
