{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Ual.Blueprint.Spec (tests) where

import Prelude

import Data.ByteString.Lazy qualified as LBS
import Data.Set qualified as Set
import Data.Text.Encoding qualified as Text
import GHC.Generics (Generic)
import PlutusTx.Blueprint.Argument (ArgumentBlueprint (..))
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Contract (ContractBlueprint (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition, definitionRef, deriveDefinitions)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Blueprint.Preamble (Preamble (..))
import PlutusTx.Blueprint.Purpose qualified as Purpose
import PlutusTx.Blueprint.Schema (Schema (..))
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo)
import PlutusTx.Blueprint.Validator
  ( AppliedArgument (..)
  , ArgumentEncoding (..)
  , ExecutionBudget (..)
  , mkValidatorBlueprint
  , validatorArguments
  , validatorBudget
  , validatorId
  , validatorRedeemer
  , validatorTitle
  )
import PlutusTx.Blueprint.Write (encodeBlueprint)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Extras (goldenVsText)

newtype Ticket = MkTicket Integer
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

{-| Hand-written rather than TH-derived: the fixture only needs *some* schema for
'Ticket', and this keeps the module free of Template Haskell. -}
instance HasBlueprintSchema Ticket referencedTypes where
  schema = SchemaBuiltInInteger emptySchemaInfo

tests :: TestTree
tests =
  testGroup
    "Blueprint"
    [ goldenVsText
        "validator arguments and budget"
        "test/Ual/Golden/validator-arguments.golden.json"
        (Text.decodeUtf8 (LBS.toStrict (encodeBlueprint contract)))
    ]

contract :: ContractBlueprint
contract =
  MkContractBlueprint
    { contractId = Just "ual-example"
    , contractPreamble =
        MkPreamble
          { preambleTitle = "UAL Example"
          , preambleDescription = Nothing
          , preambleVersion = "1.0.0"
          , preamblePlutusVersion = PlutusV3
          , preambleLicense = Nothing
          }
    , contractValidators =
        Set.singleton
          mkValidatorBlueprint
            { validatorId = Just "ticket-spend"
            , validatorTitle = "ticketSpend"
            , validatorRedeemer =
                MkArgumentBlueprint
                  { argumentTitle = Nothing
                  , argumentDescription = Nothing
                  , argumentPurpose = Set.singleton Purpose.Spend
                  , argumentSchema = definitionRef @Ticket
                  }
            , validatorArguments =
                [ MkAppliedArgument AsData (definitionRef @Ticket)
                , MkAppliedArgument AsScott (definitionRef @Integer)
                ]
            , validatorBudget = Just (MkExecutionBudget 1883313 12342)
            }
    , contractDefinitions = deriveDefinitions @[Ticket, Integer]
    }
