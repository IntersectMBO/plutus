{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Blueprint.Tests where

import Prelude

import Blueprint.Tests.Lib (Datum, Params, Redeemer, goldenJson, serialisedScript)
import Data.Set qualified as Set
import PlutusTx.Blueprint.Argument (ArgumentBlueprint (..))
import PlutusTx.Blueprint.Contract (ContractBlueprint (..))
import PlutusTx.Blueprint.Definition (definitionRef, deriveDefinitions)
import PlutusTx.Blueprint.Parameter (ParameterBlueprint (..))
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (PlutusV3))
import PlutusTx.Blueprint.Preamble (Preamble (..))
import PlutusTx.Blueprint.Purpose qualified as Purpose
import PlutusTx.Blueprint.Validator (ValidatorBlueprint (..))
import PlutusTx.Blueprint.Write (writeBlueprint)
import Test.Tasty.Extras (TestNested, testNested)

goldenTests :: TestNested
goldenTests = testNested "Blueprint" [goldenJson "Acme" (`writeBlueprint` contractBlueprint)]

contractBlueprint :: ContractBlueprint
contractBlueprint =
  MkContractBlueprint
    { contractId = Nothing
    , contractPreamble =
        MkPreamble
          { preambleTitle = "Acme Contract"
          , preambleDescription = Just "A contract that does something awesome"
          , preambleVersion = "1.1.0"
          , preamblePlutusVersion = PlutusV3
          , preambleLicense = Just "MIT"
          }
    , contractValidators =
        Set.singleton
          MkValidatorBlueprint
            { validatorTitle = "Acme Validator"
            , validatorDescription = Just "A validator that does something awesome"
            , validatorParameters =
                [ MkParameterBlueprint
                    { parameterTitle = Just "Acme Parameter"
                    , parameterDescription = Just "A parameter that does something awesome"
                    , parameterPurpose = Set.singleton Purpose.Spend
                    , parameterSchema = definitionRef @Params
                    }
                ]
            , validatorRedeemer =
                MkArgumentBlueprint
                  { argumentTitle = Just "Acme Redeemer"
                  , argumentDescription = Just "A redeemer that does something awesome"
                  , argumentPurpose = Set.fromList [Purpose.Spend, Purpose.Mint]
                  , argumentSchema = definitionRef @Redeemer
                  }
            , validatorDatum =
                Just
                  MkArgumentBlueprint
                    { argumentTitle = Just "Acme Datum"
                    , argumentDescription = Just "A datum that contains something awesome"
                    , argumentPurpose = Set.singleton Purpose.Spend
                    , argumentSchema = definitionRef @Datum
                    }
            , validatorCompiledCode = Just serialisedScript
            }
    , contractDefinitions = deriveDefinitions @[Params, Redeemer, Datum]
    }
