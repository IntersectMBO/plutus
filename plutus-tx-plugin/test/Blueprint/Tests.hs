{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Blueprint.Tests where

import Prelude

import Blueprint.Tests.Lib (Bytes, Datum, DatumPayload, Param2a, Param2b, Params, Redeemer,
                            Redeemer2, goldenJson, serialisedScript, validatorScript1,
                            validatorScript2)
import Blueprint.Tests.Lib.AsData.Blueprint (Datum2)
import Data.Set qualified as Set
import Data.Type.Equality (type (:~:) (..))
import Data.Void (Void)
import PlutusTx.Blueprint.Contract (ContractBlueprint (..))
import PlutusTx.Blueprint.Definition (UnrollAll, definitionRef, deriveDefinitions)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (PlutusV3))
import PlutusTx.Blueprint.Preamble (Preamble (..))
import PlutusTx.Blueprint.Purpose qualified as Purpose
import PlutusTx.Blueprint.TH (deriveArgumentBlueprint, deriveParameterBlueprint)
import PlutusTx.Blueprint.Validator (ValidatorBlueprint (..))
import PlutusTx.Blueprint.Write (writeBlueprint)
import PlutusTx.Builtins (BuiltinByteString, BuiltinData, BuiltinString)
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
        Set.fromList
          [ MkValidatorBlueprint
              { validatorTitle =
                  "Acme Validator #1"
              , validatorDescription =
                  Just "A validator that does something awesome"
              , validatorParameters =
                  [$(deriveParameterBlueprint ''Params (Set.singleton Purpose.Spend))]
              , validatorRedeemer =
                  $(deriveArgumentBlueprint ''Redeemer (Set.singleton Purpose.Spend))
              , validatorDatum =
                  Just $(deriveArgumentBlueprint ''Datum (Set.singleton Purpose.Spend))
              , validatorCompiledCode =
                  Just (serialisedScript validatorScript1)
              }
          , MkValidatorBlueprint
              { validatorTitle =
                  "Acme Validator #2"
              , validatorDescription =
                  Just "Another validator that does something awesome"
              , validatorParameters =
                  [ $(deriveParameterBlueprint ''Param2a (Set.singleton Purpose.Spend))
                  , $(deriveParameterBlueprint ''Param2b (Set.singleton Purpose.Mint))
                  ]
              , validatorRedeemer =
                  $(deriveArgumentBlueprint ''Redeemer2 (Set.singleton Purpose.Mint))
              , validatorDatum =
                  Just $(deriveArgumentBlueprint ''Datum2 (Set.singleton Purpose.Mint))
              , validatorCompiledCode =
                  Just (serialisedScript validatorScript2)
              }
          ]
    , contractDefinitions =
        deriveDefinitions
          @[ Params
           , Param2a
           , Param2b
           , Redeemer
           , Redeemer2
           , Datum
           , Datum2
           ]
    }

testAllRequredDefinitions ::
  UnrollAll
    [ Params
    , Param2a
    , Param2b
    , Redeemer
    , Redeemer2
    , Datum
    , Datum2
    ]
    :~: [ Params
        , Bool
        , ()
        , [Integer]
        , Integer
        , BuiltinData
        , BuiltinByteString
        , Param2a
        , Param2b
        , BuiltinString
        , Datum
        , Bytes Void
        , DatumPayload
        , Datum2
        ]
testAllRequredDefinitions = Refl
