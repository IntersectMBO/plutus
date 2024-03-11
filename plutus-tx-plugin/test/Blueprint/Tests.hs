{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

module Blueprint.Tests where

import Blueprint.Tests.Lib (goldenJson)
import Blueprint.Tests.Lib qualified as Fixture
import Data.Set qualified as Set
import PlutusTx.Blueprint
import PlutusTx.Blueprint.Purpose qualified as Purpose
import Prelude
import Test.Tasty.Extras (TestNested, testNested)

goldenTests :: TestNested
goldenTests = testNested "Blueprint" [goldenJson "Acme" (`writeBlueprint` contractBlueprint)]

-- | All the data types exposed (directly or indirectly) by the type signature of the validator
-- This type level list is used to:
-- 1. derive the schema definitions for the contract.
-- 2. make "safe" references to the [derived] schema definitions.
contractBlueprint :: Blueprint [Fixture.Params, Fixture.Redeemer, Fixture.Datum]
contractBlueprint =
  MkContractBlueprint
    { contractId = Nothing,
      contractPreamble =
        MkPreamble
          { preambleTitle = "Acme Contract",
            preambleDescription = Just "A contract that does something awesome",
            preambleVersion = "1.1.0",
            preamblePlutusVersion = PlutusV3,
            preambleLicense = Just "MIT"
          },
      contractValidators =
        Set.singleton
          MkValidatorBlueprint
            { validatorTitle = "Acme Validator",
              validatorDescription = Just "A validator that does something awesome",
              validatorParameters =
                Just $
                  pure
                    MkParameterBlueprint
                      { parameterTitle = Just "Acme Parameter",
                        parameterDescription = Just "A parameter that does something awesome",
                        parameterPurpose = Set.singleton Purpose.Spend,
                        parameterSchema = definitionRef @Fixture.Params
                      },
              validatorRedeemer =
                MkArgumentBlueprint
                  { argumentTitle = Just "Acme Redeemer",
                    argumentDescription = Just "A redeemer that does something awesome",
                    argumentPurpose = Set.fromList [Purpose.Spend, Purpose.Mint],
                    argumentSchema = definitionRef @Fixture.Redeemer
                  },
              validatorDatum =
                Just
                  MkArgumentBlueprint
                    { argumentTitle = Just "Acme Datum",
                      argumentDescription = Just "A datum that contains something awesome",
                      argumentPurpose = Set.singleton Purpose.Spend,
                      argumentSchema = definitionRef @Fixture.Datum
                    },
              validatorCompiledCode = Just Fixture.serialisedScript
            },
      contractDefinitions = deriveSchemaDefinitions
    }
