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
import Example.Ual.PurposeIsolation.Types (WitnessRedeemer)
import PlutusLedgerApi.V1.Interval qualified as Interval
import PlutusLedgerApi.V3 (serialiseCompiledCode)
import PlutusTx qualified
import PlutusTx.Assurance
import PlutusTx.Blueprint
import PlutusTx.Builtins (equalsData, unsafeDataAsB, unsafeDataAsConstr)
import PlutusTx.Prelude
import PlutusTx.Ual (ModuleUal)
import PlutusTx.Ual.TH (ualModule)
import Prelude qualified as Haskell

{-@ ONCHAIN [version: PlutusV3] [steps: 1000, semantics: E]
    spendingOnly :: BuiltinData -> BuiltinUnit
@-}
{-# INLINEABLE spendingOnly #-}
spendingOnly :: BuiltinData -> BuiltinUnit
spendingOnly raw = check (purposeTag raw == 1)

-- Inspect the V3 purpose before decoding transaction contents. This makes the
-- rejection path independent of the sizes of the transaction's lists.
{-# INLINEABLE purposeTag #-}
purposeTag :: BuiltinData -> Integer
purposeTag raw = case unsafeDataAsConstr raw of
  (contextTag, [_, _, info]) | contextTag == 0 -> case unsafeDataAsConstr info of
    (tag, _) -> tag
  _ -> traceError "malformed context"

{-@ ONCHAIN [version: PlutusV3] [steps: 1000, semantics: E]
    spendingAndMinting :: BuiltinData -> BuiltinUnit
@-}
{-# INLINEABLE spendingAndMinting #-}
spendingAndMinting :: BuiltinData -> BuiltinUnit
spendingAndMinting raw = let tag = purposeTag raw in check (tag == 1 || tag == 0)

{-@ ONCHAIN [version: PlutusV3] [steps: 1000, semantics: E]
    parameterizedSpending :: { Integer : asNative } -> BuiltinData -> BuiltinUnit
@-}
{-# INLINEABLE parameterizedSpending #-}
parameterizedSpending :: Integer -> BuiltinData -> BuiltinUnit
parameterizedSpending n raw = check (n == 7 && purposeTag raw == 1)

-- Intentionally vulnerable: ordinary transaction checks omit the purpose.
{-@ ONCHAIN [version: PlutusV3] [steps: 1000, semantics: E]
    uncheckedPurpose :: BuiltinData -> BuiltinUnit
@-}
{-# INLINEABLE uncheckedPurpose #-}
uncheckedPurpose :: BuiltinData -> BuiltinUnit
uncheckedPurpose raw = case unsafeDataAsConstr raw of
  (contextTag, [txInfo, redeemer, _]) | contextTag == 0 -> case unsafeDataAsConstr txInfo of
    (infoTag, [_, _, _, _, _, _, _, range, _, _, _, _, _, _, treasury, donation])
      | infoTag == 0 ->
          check
            ( lengthOfByteString (unsafeDataAsB redeemer)
                == 3
                && equalsData range (toBuiltinData (Interval.always :: Interval.Interval Integer))
                && equalsData treasury (toBuiltinData (Nothing :: Maybe Integer))
                && equalsData donation (toBuiltinData (Nothing :: Maybe Integer))
            )
    _ -> traceError "malformed transaction info"
  _ -> traceError "malformed context"

{-@ PROPERTY [scope: spendingOnly] [template: purpose-isolation spending] @-}
{-@ PROPERTY [scope: spendingAndMinting] [template: purpose-isolation spending minting] @-}
{-@ PROPERTY [scope: parameterizedSpending] [template: purpose-isolation spending] @-}
{-@ PROPERTY [scope: uncheckedPurpose] [template: purpose-isolation spending] @-}

-- Each positive claim is separate from its script's purpose-isolation claim.
{-@ PROPERTY [scope: spendingOnly] [template: accepts-some-context] @-}
{-@ PROPERTY [scope: spendingAndMinting] [template: accepts-some-context] @-}
{-@ PROPERTY [scope: parameterizedSpending] [template: accepts-some-context] @-}
{-@ PROPERTY [scope: uncheckedPurpose] [template: accepts-some-context] @-}

spendingCode, multiCode, uncheckedCode :: PlutusTx.CompiledCode (BuiltinData -> BuiltinUnit)
spendingCode = $$(PlutusTx.compile [||spendingOnly||])
multiCode = $$(PlutusTx.compile [||spendingAndMinting||])
uncheckedCode = $$(PlutusTx.compile [||uncheckedPurpose||])

parameterizedCode :: PlutusTx.CompiledCode (Integer -> BuiltinData -> BuiltinUnit)
parameterizedCode = $$(PlutusTx.compile [||parameterizedSpending||])

blueprint :: ContractBlueprint
blueprint =
  MkContractBlueprint
    { contractId = Just "ual-purpose-isolation"
    , contractPreamble = MkPreamble "Purpose isolation templates" Nothing "1.0.0" PlutusV3 Nothing
    , contractValidators =
        Set.fromList
          [ mkValidatorBlueprint
              { validatorId = Just ident
              , validatorTitle = ident
              , validatorParameters =
                  if ident Haskell.== "parameterizedSpending"
                    then
                      [MkParameterBlueprint Nothing Nothing (Set.singleton Spend) (SchemaBuiltInInteger emptySchemaInfo)]
                    else []
              , -- These are invocation metadata. Template parameters independently
                -- define the assertion, including the spending+minting claim above.
                validatorRedeemer =
                  MkArgumentBlueprint
                    Nothing
                    Nothing
                    (Set.singleton Spend)
                    ( if ident Haskell.== "uncheckedPurpose"
                        then definitionRef @WitnessRedeemer
                        else definitionRef @BuiltinData
                    )
              , validatorCompiled = Just (compiledValidator PlutusV3 (SBS.fromShort bytes))
              }
          | (ident, bytes) <-
              [ ("spendingOnly", serialiseCompiledCode spendingCode)
              , ("spendingAndMinting", serialiseCompiledCode multiCode)
              , ("uncheckedPurpose", serialiseCompiledCode uncheckedCode)
              , ("parameterizedSpending", serialiseCompiledCode parameterizedCode)
              ]
          ]
    , contractDefinitions = deriveDefinitions @'[BuiltinData, Integer, WitnessRedeemer]
    }

$(Haskell.pure [])
annotations :: ModuleUal
annotations = $(ualModule)

main :: Haskell.IO ()
main = do
  let preamble =
        MkAssurancePreamble
          "Purpose isolation examples"
          Nothing
          (Just "1.0.0")
          ["Plutus contributors"]
          "2026-11-01"
          Nothing
  defaultMainInterfaceBundle preamble "" [annotations] blueprint
