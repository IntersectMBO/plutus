{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Ual.Resolve.Spec (tests) where

import Prelude

import Data.Aeson ((.=))
import Data.Aeson qualified as Aeson
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Either (isRight)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Vector qualified as V
import GHC.Generics (Generic)
import PlutusTx.Blueprint.Argument (ArgumentBlueprint (..))
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Contract (ContractBlueprint (..))
import PlutusTx.Blueprint.Definition
  ( HasBlueprintDefinition
  , definitionId
  , definitionRef
  , deriveDefinitions
  )
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Blueprint.Preamble (Preamble (..))
import PlutusTx.Blueprint.Purpose qualified as Purpose
import PlutusTx.Blueprint.Schema (Schema (..))
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo)
import PlutusTx.Blueprint.Validator
  ( AppliedArgument (..)
  , ExecutionBudget (..)
  , ValidatorBlueprint
  , mkValidatorBlueprint
  , validatorArguments
  , validatorId
  , validatorRedeemer
  , validatorTitle
  )
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Resolve (attachUal)
import PlutusTx.Ual.Syntax
  ( ArgumentEncoding (..)
  , ModuleUal (..)
  , OnchainDecl (..), OnchainKind (..)
  , ResolvedArgument (..)
  , UalArgument (..)
  , UalModuleName (..)
  , emptyModuleUal
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

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
    "Resolve"
    [ testCase "fills arguments on the matching validator" $
        (>>= lookupKey "arguments") . firstValidator
          <$> attachUal [uals decl] (contract [validator (Just "v")])
          @?= Right
            ( Just
                ( Aeson.Array
                    ( V.fromList
                        [ Aeson.object ["encoding" .= ("asData" :: Text), "schema" .= ticketRef]
                        , Aeson.object ["encoding" .= ("asScott" :: Text), "schema" .= integerRef]
                        ]
                    )
                )
            )
    , testCase "fills the budget" $
        (>>= lookupKey "budget") . firstValidator
          <$> attachUal
            [uals decl {onchainBudget = Just (MkExecutionBudget 7 8)}]
            (contract [validator (Just "v")])
          @?= Right (Just (Aeson.object ["exCPU" .= (7 :: Integer), "exMem" .= (8 :: Integer)]))
    , testCase "no ONCHAIN blocks leaves the validator without arguments" $
        (>>= lookupKey "arguments") . firstValidator
          <$> attachUal [] (contract [validator (Just "v")])
          @?= Right Nothing
    , testCase "matching version is accepted" $
        assertBool "should succeed" . isRight $
          attachUal
            [uals decl {onchainVersion = Just PlutusV3}]
            (contract [validator (Just "v")])
    , testCase "version disagreement is reported" $
        errorsOf
          ( attachUal
              [uals decl {onchainVersion = Just PlutusV2}]
              (contract [validator (Just "v")])
          )
          @?= Just [VersionMismatch "v" "PlutusV2" "PlutusV3"]
    , testCase "ONCHAIN with no matching validator is reported" $
        errorsOf (attachUal [uals decl] (contract [validator (Just "other")]))
          @?= Just [NoValidatorForOnchain "v"]
    , testCase "validator with no id and no ONCHAIN block is fine" $
        assertBool "should succeed" . isRight $
          attachUal [] (contract [validator Nothing])
    , testCase "arguments with no ONCHAIN block are reported" $
        errorsOf
          ( attachUal
              []
              ( contract
                  [ (validator (Just "v"))
                      { validatorArguments = [MkAppliedArgument AsData (definitionRef @Ticket)]
                      }
                  ]
              )
          )
          @?= Just [OrphanValidatorArguments "v"]
    , testCase "duplicate ONCHAIN names are reported" $
        errorsOf (attachUal [uals decl, uals decl] (contract [validator (Just "v")]))
          @?= Just [DuplicateOnchain "v"]
    , testCase "unresolved argument lists are reported" $
        errorsOf (attachUal [uals decl {onchainResolvedArgs = []}] (contract [validator (Just "v")]))
          @?= Just [UnresolvedArguments "v"]
    , testCase "duplicate validator ids are reported" $
        errorsOf (attachUal [] (contract [validator (Just "dup"), validator2 (Just "dup")]))
          @?= Just [DuplicateValidatorId "dup"]
    ]

decl :: OnchainDecl
decl =
  MkOnchainDecl
    { onchainKind = Script
    , onchainResolvedResult = Nothing
    , onchainName = "v"
    , onchainArgs = [MkUalArgument "Ticket" AsData, MkUalArgument "Integer" AsScott]
    , onchainResult = "()"
    , onchainVersion = Nothing
    , onchainBudget = Nothing
    , onchainLine = 1
    , onchainResolvedArgs =
        [ MkResolvedArgument AsData (definitionId @Ticket)
        , MkResolvedArgument AsScott (definitionId @Integer)
        ]
    }

uals :: OnchainDecl -> ModuleUal
uals d = (emptyModuleUal (UalModuleName "M")) {ualOnchain = [d]}

validator :: Maybe Text -> ValidatorBlueprint '[Ticket, Integer]
validator vid =
  mkValidatorBlueprint
    { validatorId = vid
    , validatorTitle = "first"
    , validatorRedeemer =
        MkArgumentBlueprint
          { argumentTitle = Nothing
          , argumentDescription = Nothing
          , argumentPurpose = Set.singleton Purpose.Spend
          , argumentSchema = definitionRef @Ticket
          }
    }

validator2 :: Maybe Text -> ValidatorBlueprint '[Ticket, Integer]
validator2 vid = (validator vid) {validatorTitle = "second"}

contract :: [ValidatorBlueprint '[Ticket, Integer]] -> ContractBlueprint
contract vs =
  MkContractBlueprint
    { contractId = Nothing
    , contractPreamble =
        MkPreamble
          { preambleTitle = "t"
          , preambleDescription = Nothing
          , preambleVersion = "1"
          , preamblePlutusVersion = PlutusV3
          , preambleLicense = Nothing
          }
    , contractValidators = Set.fromList vs
    , contractDefinitions = deriveDefinitions @[Ticket, Integer]
    }

{-| The reported errors, if the call failed. @ContractBlueprint@ has no 'Eq' and
no 'Show', so the result of a failing call cannot be compared as an @Either@; this
throws away the success side, which the assertions using it never take. -}
errorsOf :: Either [UalError] ContractBlueprint -> Maybe [UalError]
errorsOf = either Just (const Nothing)

{-| The first validator's JSON. @ContractBlueprint@ is existential, so a caller
that has not built it cannot pattern-match a validator out of it and keep the
@referencedTypes@ index; the encoded document is the index-agnostic view. -}
firstValidator :: ContractBlueprint -> Maybe Aeson.Value
firstValidator bp = case Aeson.toJSON bp of
  Aeson.Object o -> case KeyMap.lookup "validators" o of
    Just (Aeson.Array vs) | not (V.null vs) -> Just (vs V.! 0)
    _ -> Nothing
  _ -> Nothing

lookupKey :: Text -> Aeson.Value -> Maybe Aeson.Value
lookupKey k = \case
  Aeson.Object o -> KeyMap.lookup (Key.fromText k) o
  _ -> Nothing

ticketRef, integerRef :: Aeson.Value
ticketRef = Aeson.toJSON (definitionRef @Ticket :: Schema '[Ticket, Integer])
integerRef = Aeson.toJSON (definitionRef @Integer :: Schema '[Ticket, Integer])
