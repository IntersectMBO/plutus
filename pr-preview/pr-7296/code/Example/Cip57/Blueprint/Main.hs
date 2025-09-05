-- BEGIN pragmas
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.0.0 #-}

-- END pragmas

module Main where

-- BEGIN imports
import PlutusTx.Blueprint

import PlutusTx.Prelude

import Data.Set qualified as Set
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.DCert qualified as V1
import PlutusLedgerApi.V1.Time qualified as V1
import PlutusLedgerApi.V1.Tx qualified as V1
import PlutusLedgerApi.V3 qualified as V3
import PlutusTx.AssocMap (Map)
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)

-- END imports

import Paths_docusaurus_examples (getDataFileName)
import Prelude (FilePath, IO)

-- BEGIN MyParams annotations

{-# ANN MkMyParams (SchemaTitle "Title for the MyParams definition") #-}
{-# ANN MkMyParams (SchemaDescription "Description for the MyParams definition") #-}

-- END MyParams annotations
-- BEGIN MyRedeemer annotations

{-# ANN R0 (SchemaComment "Redeemer 0") #-}
{-# ANN R1 (SchemaComment "Redeemer 1") #-}
{-# ANN R2 (SchemaComment "Redeemer 2") #-}

-- END MyRedeemer annotations
-- BEGIN interface types

type MyDatum = Integer

data MyRedeemer = R0 | R1 V3.Lovelace | R2 V3.Value

data MyParams = MkMyParams
  { myBool          :: Bool
  , myInteger       :: Integer
  , myMap           :: Map Integer Bool
  , myDCert         :: V1.DCert
  , myScriptTag     :: V1.ScriptTag
  , myRedeemerPtr   :: V1.RedeemerPtr
  , myDiffMillis    :: V1.DiffMilliSeconds
  , myTxId          :: V3.TxId
  , myTokenName     :: V3.TokenName
  , myAddress       :: V3.Address
  , myPubKey        :: V3.PubKeyHash
  , myPOSIXTime     :: V3.POSIXTime
  , myLedgerBytes   :: V3.LedgerBytes
  , myCredential    :: V3.Credential
  , myDatum         :: V3.Datum
  , myLovelace      :: V3.Lovelace
  , myInterval      :: V3.Interval Integer
  , myScriptHash    :: V3.ScriptHash
  , myRedeemer      :: V3.Redeemer
  , myRedeemerHash  :: V3.RedeemerHash
  , myDatum_        :: V3.Datum
  , myDatumHash     :: V3.DatumHash
  , myTxInInfo      :: V3.TxInInfo
  , myTxInfo        :: V3.TxInfo
  , myScriptPurpose :: V3.ScriptPurpose
  , myScriptContext :: V3.ScriptContext
  }

-- END interface types
-- BEGIN makeIsDataSchemaIndexed

$(makeIsDataSchemaIndexed ''MyParams [('MkMyParams, 0)])
$(makeIsDataSchemaIndexed ''MyRedeemer [('R0, 0), ('R1, 1), ('R2, 2)])

-- END makeIsDataSchemaIndexed
-- BEGIN derived instances

deriving stock instance Generic MyParams
deriving anyclass instance HasBlueprintDefinition MyParams

deriving stock instance Generic MyRedeemer
deriving anyclass instance HasBlueprintDefinition MyRedeemer

-- END derived instances
-- BEGIN validator

typedValidator :: MyParams -> MyDatum -> MyRedeemer -> Bool
typedValidator MkMyParams{..} datum redeemer =
  case redeemer of
    R0   -> myBool
    R1{} -> myBool
    R2{} -> myInteger == datum

untypedValidator :: MyParams -> BuiltinData -> BuiltinUnit
untypedValidator params scriptContext =
  check
    $ case V3.unsafeFromBuiltinData scriptContext of
      V3.ScriptContext
        _txInfo
        (V3.Redeemer redeemer)
        (V3.SpendingScript _ (Just (V3.Datum datum))) ->
          typedValidator
            params
            (V3.unsafeFromBuiltinData datum)
            (V3.unsafeFromBuiltinData redeemer)
      _ -> False

-- END validator
-- BEGIN contract blueprint declaration

myContractBlueprint :: ContractBlueprint
myContractBlueprint =
  MkContractBlueprint
    { contractId = Just "my-contract"
    , contractPreamble = myPreamble -- defined below
    , contractValidators = Set.singleton myValidator -- defined below
    , contractDefinitions = deriveDefinitions @[MyParams, MyDatum, MyRedeemer]
    }

-- END contract blueprint declaration
-- BEGIN preamble declaration

myPreamble :: Preamble
myPreamble =
  MkPreamble
    { preambleTitle = "My Contract"
    , preambleDescription = Just "A simple contract"
    , preambleVersion = "1.0.0"
    , preamblePlutusVersion = PlutusV2
    , preambleLicense = Just "MIT"
    }

-- END preamble declaration
-- BEGIN validator blueprint declaration

myValidator =
  MkValidatorBlueprint
    { validatorTitle = "My Validator"
    , validatorDescription = Just "An example validator"
    , validatorParameters =
        [ MkParameterBlueprint
            { parameterTitle = Just "My Validator Parameters"
            , parameterDescription = Just "Compile-time validator parameters"
            , parameterPurpose = Set.singleton Spend
            , parameterSchema = definitionRef @MyParams
            }
        ]
    , validatorRedeemer =
        MkArgumentBlueprint
          { argumentTitle = Just "My Redeemer"
          , argumentDescription = Just "A redeemer that does something awesome"
          , argumentPurpose = Set.fromList [Spend, Mint]
          , argumentSchema = definitionRef @MyRedeemer
          }
    , validatorDatum =
        Just
          MkArgumentBlueprint
            { argumentTitle = Just "My Datum"
            , argumentDescription = Just "A datum that contains something awesome"
            , argumentPurpose = Set.singleton Spend
            , argumentSchema = definitionRef @MyDatum
            }
    , validatorCompiled = Nothing -- you can optionally provide the compiled code here
    }

-- END validator blueprint declaration
-- BEGIN write blueprint to file

-- >>> writeBlueprintToFile "plutus.json"
writeBlueprintToFile :: FilePath -> IO ()
writeBlueprintToFile path = writeBlueprint path myContractBlueprint

-- END write blueprint to file

main :: IO ()
main = writeBlueprintToFile =<< getDataFileName "plutus.json"
