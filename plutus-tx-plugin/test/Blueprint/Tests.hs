{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Blueprint.Tests where

import Blueprint.Tests.Lib (goldenJson)
import Blueprint.Tests.Lib qualified as Fixture
import Data.Set qualified as Set
import Data.Void (Void)
import PlutusTx.Blueprint
import PlutusTx.Blueprint.Purpose qualified as Purpose
import PlutusTx.Builtins.Internal (BuiltinByteString, BuiltinData)
import Prelude
import Test.Tasty.Extras (TestNested, testNested)

goldenTests :: TestNested
goldenTests = testNested "Blueprint" [goldenJson "Acme" (`writeBlueprint` contractBlueprint)]

{- | The contract blueprint is indexed by a type-level list of schema definitions.

This list is inferred automatically from the contract definitions, and is used to make references
to the schema definitions safe.
-}
contractBlueprint :: Blueprint
contractBlueprint =
  MkBlueprint
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
                  Just $
                    pure
                      MkParameterBlueprint
                        { parameterTitle = Just "Acme Parameter"
                        , parameterDescription = Just "A parameter that does something awesome"
                        , parameterPurpose = Set.singleton Purpose.Spend
                        , parameterSchema = definitionRef @Fixture.Params
                        }
              , validatorRedeemer =
                  MkArgumentBlueprint
                    { argumentTitle = Just "Acme Redeemer"
                    , argumentDescription = Just "A redeemer that does something awesome"
                    , argumentPurpose = Set.fromList [Purpose.Spend, Purpose.Mint]
                    , argumentSchema = definitionRef @Fixture.Redeemer
                    }
              , validatorDatum =
                  Just
                    MkArgumentBlueprint
                      { argumentTitle = Just "Acme Datum"
                      , argumentDescription = Just "A datum that contains something awesome"
                      , argumentPurpose = Set.singleton Purpose.Spend
                      , argumentSchema = definitionRef @Fixture.Datum
                      }
              , validatorCompiledCode = Just Fixture.serialisedScript
              }
      , contractDefinitions =
          NoDefinitions
            `addDefinition` definition @()
            `addDefinition` definition @Bool
            `addDefinition` definition @Integer
            `addDefinition` definition @BuiltinData
            `addDefinition` definition @BuiltinByteString
            `addDefinition` definition @Fixture.Params
            `addDefinition` definition @Fixture.Redeemer
            `addDefinition` definition @(Fixture.Bytes Void)
            `addDefinition` definition @Fixture.DatumPayload
            `addDefinition` definition @Fixture.Datum
      }
