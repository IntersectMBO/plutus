-- BLOCK1
-- BEGIN pragmas
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
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
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.0.0 #-}

-- END pragmas

module Main where

-- BLOCK2
-- BEGIN imports
import PlutusTx.Blueprint

import PlutusTx.Prelude

import Data.Set qualified as Set
import GHC.Generics (Generic)
import Paths_docusaurus_examples (getDataFileName)
import PlutusLedgerApi.V3 (Datum (..), Redeemer (..), ScriptContext (..),
                           ScriptInfo (SpendingScript), UnsafeFromData (..))
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)
import Prelude (FilePath, IO)

-- END imports
-- BLOCK3
-- BEGIN MyParams annotations

{-# ANN MkMyParams (SchemaTitle "Title for the MyParams definition") #-}
{-# ANN MkMyParams (SchemaDescription "Description for the MyParams definition") #-}

-- END MyParams annotations
-- BLOCK4
-- BEGIN MyRedeemer annotations

{-# ANN R1 (SchemaComment "Left redeemer") #-}
{-# ANN R2 (SchemaComment "Right redeemer") #-}

-- END MyRedeemer annotations
-- BLOCK5
-- BEGIN interface types

type MyDatum = Integer

data MyRedeemer = R1 | R2

data MyParams = MkMyParams
  { myBool    :: Bool
  , myInteger :: Integer
  }

-- END interface types
-- BLOCK6
-- BEGIN makeIsDataSchemaIndexed MyParams

$(makeIsDataSchemaIndexed ''MyParams [('MkMyParams, 0)])
$(makeIsDataSchemaIndexed ''MyRedeemer [('R1, 0), ('R2, 1)])

-- END makeIsDataSchemaIndexed MyParams
-- BLOCK7
-- BEGIN generic instances

deriving stock instance (Generic MyParams)
deriving stock instance (Generic MyRedeemer)

-- END generic instances
-- BLOCK8
-- BEGIN AsDefinitionId instances

deriving anyclass instance (AsDefinitionId MyParams)
deriving anyclass instance (AsDefinitionId MyRedeemer)

-- END AsDefinitionId instances
-- BLOCK9
-- BEGIN validator

typedValidator :: MyParams -> MyDatum -> MyRedeemer -> Bool
typedValidator MkMyParams{..} datum redeemer =
  case redeemer of
    R1 -> myBool
    R2 -> myInteger == datum

untypedValidator :: MyParams -> BuiltinData -> BuiltinUnit
untypedValidator params scriptContext =
  check
    $ case unsafeFromBuiltinData scriptContext of
      ScriptContext
        _txInfo
        (Redeemer redeemer)
        (SpendingScript _ (Just (Datum datum))) ->
          typedValidator params (unsafeFromBuiltinData datum) (unsafeFromBuiltinData redeemer)
      _ -> False

-- END validator
-- BLOCK10
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
-- BLOCK11
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
-- BLOCK12
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
    , validatorCompiledCode = Nothing -- you can optionally provide the compiled code here
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
