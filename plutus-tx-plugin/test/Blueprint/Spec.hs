{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

module Blueprint.Spec where

import PlutusTx.Blueprint
import Prelude

import Blueprint.Fixture qualified as Fixture
import Control.Monad.Reader (asks)
import Data.Set qualified as Set
import PlutusCore.Crypto.Hash (blake2b_224)
import PlutusTx.Blueprint.Purpose qualified as Purpose
import System.FilePath ((</>))
import Test.Tasty (TestName)
import Test.Tasty.Extras (TestNested, testNested)
import Test.Tasty.Golden (goldenVsFile)

goldenTests :: TestNested
goldenTests = testNested "Blueprint" [goldenBlueprint "Acme" acmeContractBlueprint]

goldenBlueprint :: TestName -> ContractBlueprint -> TestNested
goldenBlueprint name blueprint = do
  goldenPath <- asks $ foldr (</>) name
  let actual = goldenPath ++ ".actual.json"
  let golden = goldenPath ++ ".golden.json"
  pure $ goldenVsFile name golden actual (writeBlueprint actual blueprint)

type DataTypes =
  [ Fixture.AcmeDatum
  , Fixture.AcmeDatumPayload
  , Fixture.AcmeParams
  , Fixture.AcmeRedeemer
  , Fixture.AcmeBytes
  ]

acmeContractBlueprint :: ContractBlueprint
acmeContractBlueprint =
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
        [ MkValidatorBlueprint
            { validatorTitle = "Acme Validator"
            , validatorDescription = Just "A validator that does something awesome"
            , validatorParameters =
                Just
                  $ pure
                    MkParameterBlueprint
                      { parameterTitle = Just "Acme Parameter"
                      , parameterDescription = Just "A parameter that does something awesome"
                      , parameterPurpose = Set.singleton Purpose.Spend
                      , parameterSchema = schemaRef @Fixture.AcmeParams @DataTypes
                      }
            , validatorRedeemer =
                MkArgumentBlueprint
                  { argumentTitle = Just "Acme Redeemer"
                  , argumentDescription = Just "A redeemer that does something awesome"
                  , argumentPurpose = Set.fromList [Purpose.Spend, Purpose.Mint]
                  , argumentSchema = schemaRef @Fixture.AcmeRedeemer @DataTypes
                  }
            , validatorDatum =
                Just
                  MkArgumentBlueprint
                    { argumentTitle = Just "Acme Datum"
                    , argumentDescription = Just "A datum that contains something awesome"
                    , argumentPurpose = Set.singleton Purpose.Spend
                    , argumentSchema = schemaRef @Fixture.AcmeDatum @DataTypes
                    }
            , validatorCompiledCode =
                Just
                  MkCompiledCode
                    { compiledCodeBytes = Fixture.serialisedScript
                    , compiledCodeHash = blake2b_224 Fixture.serialisedScript
                    }
            }
        ]
    , contractDefinitions = deriveSchemaDefinitions @DataTypes
    }
