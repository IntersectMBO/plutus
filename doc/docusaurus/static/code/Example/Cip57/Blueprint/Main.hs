-- BLOCK1
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
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.0.0 #-}

-- END pragmas

module Main where

-- BLOCK2
-- BEGIN imports
import PlutusTx.Blueprint

import PlutusTx.Prelude

import AuctionMintingPolicy
import Data.ByteString.Short qualified as Short
import Data.Set qualified as Set
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.DCert qualified as V1
import PlutusLedgerApi.V1.Time qualified as V1
import PlutusLedgerApi.V1.Tx qualified as V1
import PlutusLedgerApi.V3 qualified as V3
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)

-- END imports

import Paths_docusaurus_examples (getDataFileName)
import Prelude (FilePath, IO)

-- BLOCK3
-- BEGIN MyParams annotations

-- {-# ANN MkMyParams (SchemaTitle "Title for the MyParams definition") #-}
-- {-# ANN MkMyParams (SchemaDescription "Description for the MyParams definition") #-}

-- END MyParams annotations
-- BLOCK4
-- BEGIN MyRedeemer annotations

-- {-# ANN R0 (SchemaComment "Redeemer 0") #-}
-- {-# ANN R1 (SchemaComment "Redeemer 1") #-}
-- {-# ANN R2 (SchemaComment "Redeemer 2") #-}

-- END MyRedeemer annotations
-- BLOCK5
-- BEGIN interface types

-- type MyDatum = Integer

-- data MyRedeemer = R0 | R1 V3.Lovelace | R2 V3.Value

-- data MyParams = MkMyParams
--   { myBool          :: Bool
--   , myInteger       :: Integer
--   , myDCert         :: V1.DCert
--   , myScriptTag     :: V1.ScriptTag
--   , myRedeemerPtr   :: V1.RedeemerPtr
--   , myDiffMillis    :: V1.DiffMilliSeconds
--   , myTxId          :: V3.TxId
--   , myTokenName     :: V3.TokenName
--   , myAddress       :: V3.Address
--   , myPubKey        :: V3.PubKeyHash
--   , myPOSIXTime     :: V3.POSIXTime
--   , myLedgerBytes   :: V3.LedgerBytes
--   , myCredential    :: V3.Credential
--   , myDatum         :: V3.Datum
--   , myLovelace      :: V3.Lovelace
--   , myInterval      :: V3.Interval Integer
--   , myScriptHash    :: V3.ScriptHash
--   , myRedeemer      :: V3.Redeemer
--   , myRedeemerHash  :: V3.RedeemerHash
--   , myDatum_        :: V3.Datum
--   , myDatumHash     :: V3.DatumHash
--   , myTxInInfo      :: V3.TxInInfo
--   , myTxInfo        :: V3.TxInfo
--   , myScriptPurpose :: V3.ScriptPurpose
--   , myScriptContext :: V3.ScriptContext
--   }

-- END interface types
-- BLOCK6
-- BEGIN makeIsDataSchemaIndexed MyParams

-- $(makeIsDataSchemaIndexed ''MyParams [('MkMyParams, 0)])
-- $(makeIsDataSchemaIndexed ''MyRedeemer [('R0, 0), ('R1, 1), ('R2, 2)])

-- END makeIsDataSchemaIndexed MyParams
-- BLOCK7
-- BEGIN generic instances

-- deriving stock instance Generic MyParams
-- deriving stock instance Generic MyRedeemer

-- END generic instances
-- BLOCK8
-- BEGIN HasBlueprintDefinition instances

-- deriving anyclass instance HasBlueprintDefinition MyParams
-- deriving anyclass instance HasBlueprintDefinition MyRedeemer

-- END HasBlueprintDefinition instances
-- BLOCK9
-- BEGIN validator

-- typedValidator :: MyParams -> MyDatum -> MyRedeemer -> Bool
-- typedValidator MkMyParams{..} datum redeemer =
--   case redeemer of
--     R0   -> myBool
--     R1{} -> myBool
--     R2{} -> myInteger == datum

-- untypedValidator :: MyParams -> BuiltinData -> BuiltinUnit
-- untypedValidator params scriptContext =
--   check
--     $ case V3.unsafeFromBuiltinData scriptContext of
--       V3.ScriptContext
--         _txInfo
--         (V3.Redeemer redeemer)
--         (V3.SpendingScript _ (Just (V3.Datum datum))) ->
--           typedValidator
--             params
--             (V3.unsafeFromBuiltinData datum)
--             (V3.unsafeFromBuiltinData redeemer)
--       _ -> False

-- END validator
-- BLOCK10
-- BEGIN contract blueprint declaration

myContractBlueprint :: ContractBlueprint
myContractBlueprint =
  MkContractBlueprint
    { contractId = Just "auction-minting-policy"
    , contractPreamble = myPreamble -- defined below
    , contractValidators = Set.singleton myValidator -- defined below
    , contractDefinitions = deriveDefinitions @[AuctionMintingParams, ()]
    }

-- END contract blueprint declaration
-- BLOCK11
-- BEGIN preamble declaration

myPreamble :: Preamble
myPreamble =
  MkPreamble
    { preambleTitle = "Auction Minting Policy"
    , preambleDescription = Just "A simple minting policy"
    , preambleVersion = "1.0.0"
    , preamblePlutusVersion = PlutusV2
    , preambleLicense = Just "MIT"
    }

-- END preamble declaration
-- BLOCK12
-- BEGIN validator blueprint declaration

myValidator =
  MkValidatorBlueprint
    { validatorTitle = "Auction Minting Validator"
    , validatorDescription = Just "A simple minting validator"
    , validatorParameters =
        [ MkParameterBlueprint
            { parameterTitle = Just "Minting Validator Parameters"
            , parameterDescription = Just "Compile-time validator parameters"
            , parameterPurpose = Set.singleton Mint
            , parameterSchema = definitionRef @AuctionMintingParams
            }
        ]
    , validatorRedeemer =
        MkArgumentBlueprint
          { argumentTitle = Just "Redeemer for the minting policy"
          , argumentDescription = Just "The minting policy does not use a redeemer, hence ()"
          , argumentPurpose = Set.fromList [Mint]
          , argumentSchema = definitionRef @()
          }
    , validatorDatum = Nothing
    , validatorCompiledCode = Just . Short.fromShort . V3.serialiseCompiledCode
        $ auctionMintingPolicyScript "0e20ac97864bbc44b7742f4ad7cbf065d1c077643ce844f2f4909f0b"
    }

-- END validator blueprint declaration
-- BLOCK13
-- BEGIN write blueprint to file

-- >>> writeBlueprintToFile "plutus.json"
writeBlueprintToFile :: FilePath -> IO ()
writeBlueprintToFile path = writeBlueprint path myContractBlueprint

-- END write blueprint to file

main :: IO ()
main = writeBlueprintToFile =<< getDataFileName "plutus.json"
