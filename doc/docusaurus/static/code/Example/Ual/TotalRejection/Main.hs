{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-full-laziness -fno-ignore-interface-pragmas -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr -fno-specialise -fno-strictness #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:target-version=1.1.0 #-}

module Main where

import Data.ByteString.Short qualified as SBS
import Data.Set qualified as Set
import PlutusLedgerApi.V3 (serialiseCompiledCode)
import PlutusTx qualified
import PlutusTx.Assurance
import PlutusTx.Blueprint
import PlutusTx.Builtins (unsafeDataAsConstr)
import PlutusTx.Prelude
import PlutusTx.Ual (ModuleUal)
import PlutusTx.Ual.TH (ualModule)
import Prelude qualified as Haskell

-- Inspect the V3 script purpose before testing a contradictory condition.
-- Malformed contexts fail; no well-formed purpose can have both tags. The
-- source is deliberately not a constant-error script.
{-@ ONCHAIN [version: PlutusV3] [steps: 1000, semantics: E]
    locked :: BuiltinData -> BuiltinUnit
@-}
{-# INLINEABLE locked #-}
locked :: BuiltinData -> BuiltinUnit
locked raw = let tag = purposeTag raw in check (tag == 1 && tag == 0)

{-# INLINEABLE purposeTag #-}
purposeTag :: BuiltinData -> Integer
purposeTag raw = case unsafeDataAsConstr raw of
  (contextTag, [_, _, info]) | contextTag == 0 -> case unsafeDataAsConstr info of
    (tag, _) -> tag
  _ -> traceError "malformed context"

{-@ PROPERTY [scope: locked] [template: accepts-some-context] @-}

lockedCode :: PlutusTx.CompiledCode (BuiltinData -> BuiltinUnit)
lockedCode = $$(PlutusTx.compile [||locked||])

blueprint :: ContractBlueprint
blueprint =
  MkContractBlueprint
    { contractId = Just "ual-total-rejection"
    , contractPreamble = MkPreamble "Total rejection example" Nothing "1.0.0" PlutusV3 Nothing
    , contractValidators =
        Set.singleton
          mkValidatorBlueprint
            { validatorId = Just "locked"
            , validatorTitle = "locked"
            , validatorParameters = []
            , validatorRedeemer =
                MkArgumentBlueprint Nothing Nothing (Set.singleton Spend) (definitionRef @BuiltinData)
            , validatorCompiled =
                Just (compiledValidator PlutusV3 (SBS.fromShort (serialiseCompiledCode lockedCode)))
            }
    , contractDefinitions = deriveDefinitions @'[BuiltinData]
    }

$(Haskell.pure [])
annotations :: ModuleUal
annotations = $(ualModule)

main :: Haskell.IO ()
main = do
  let preamble =
        MkAssurancePreamble
          "Plinth total rejection example"
          Nothing
          (Just "1.0.0")
          ["Plutus contributors"]
          "2026-11-05"
          Nothing
  defaultMainInterfaceBundle preamble "" [annotations] blueprint
