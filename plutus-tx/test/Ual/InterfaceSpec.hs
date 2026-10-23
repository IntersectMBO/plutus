{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Ual.InterfaceSpec (tests) where

import Data.Aeson (encode)
import Data.ByteString.Lazy.Char8 qualified as LBS
import Data.Either (isLeft)
import Data.List (isInfixOf)
import Data.Set qualified as Set
import PlutusTx.Assurance.Interface (interfaceBlueprint)
import PlutusTx.Blueprint
import PlutusTx.Builtins (BuiltinData)
import PlutusTx.Ual.Syntax
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase)
import Prelude

bp :: ContractBlueprint
bp =
  MkContractBlueprint
    Nothing
    (MkPreamble "test" Nothing "1" PlutusV3 Nothing)
    ( Set.singleton
        mkValidatorBlueprint
          { validatorId = Just "test"
          , validatorTitle = "test"
          , validatorParameters =
              [MkParameterBlueprint Nothing Nothing (Set.singleton Mint) (SchemaBuiltInInteger emptySchemaInfo)]
          , validatorRedeemer =
              MkArgumentBlueprint Nothing Nothing (Set.singleton Mint) (definitionRef @BuiltinData)
          }
    )
    (deriveDefinitions @'[Integer, BuiltinData])

annotations :: ArgumentEncoding -> ModuleUal
annotations enc =
  (emptyModuleUal (UalModuleName "Test"))
    { ualOnchain =
        [ MkOnchainDecl
            "test"
            Script
            [MkUalArgument "Integer" enc, MkUalArgument "BuiltinData" AsData]
            "BuiltinUnit"
            (Just PlutusV3)
            (Just (MkSemanticStepBudget 100 "E"))
            1
            Nothing
            [ MkResolvedArgument enc (definitionIdFromType @Integer)
            , MkResolvedArgument AsData (definitionIdFromType @BuiltinData)
            ]
        ]
    }

tests :: TestTree
tests =
  testGroup
    "compiled interface"
    [ testCase "native parameter schema is preserved and referenced" $
        case interfaceBlueprint [annotations AsNative] bp of
          Left err -> assertFailure err
          Right value -> do
            let output = LBS.unpack (encode value)
            assertBool "absent optional fields are omitted" (not ("null" `isInfixOf` output))
            assertBool "native wire type" ("#integer" `isInfixOf` output)
            assertBool "ordered parameter reference" ("/parameters/0" `isInfixOf` output)
            assertBool "dialect" ("compiled-interface/v1/schema.json" `isInfixOf` output)
            assertBool "budget is separate" (not ("\"budget\"" `isInfixOf` output))
            assertBool "no encoding override" (not ("\"encoding\"" `isInfixOf` output))
    , testCase "Data annotation cannot relabel a native parameter" $
        assertBool "encoding mismatch rejected" (isLeft (interfaceBlueprint [annotations AsData] bp))
    , testCase "Scott annotation is explicitly unsupported" $
        assertBool "Scott rejected" (isLeft (interfaceBlueprint [annotations AsScott] bp))
    , testCase "unresolved annotations are rejected" $
        let m = annotations AsNative
            ds = [d {onchainResolvedArgs = []} | d <- ualOnchain m]
         in assertBool "unresolved rejected" (isLeft (interfaceBlueprint [m {ualOnchain = ds}] bp))
    ]
