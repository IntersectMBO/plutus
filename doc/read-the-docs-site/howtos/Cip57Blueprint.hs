-- BEGIN pragmas
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE Strict               #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

-- END pragmas

module Cip57Blueprint where

-- BEGIN imports
import PlutusTx.Blueprint

import Data.ByteString (ByteString)
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import GHC.Generics (Generic)
import PlutusLedgerApi.V3 (BuiltinData, ScriptContext, UnsafeFromData (..))
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude (check)

-- END imports
-- BEGIN MyParams annotations

{-# ANN MkMyParams (SchemaTitle "Title for the MyParams definition") #-}
{-# ANN MkMyParams (SchemaDescription "Description for the MyParams definition") #-}

-- END MyParams annotations
-- BEGIN MyRedeemer annotations

{-# ANN R1 (SchemaComment "Left redeemer") #-}
{-# ANN R2 (SchemaComment "Right redeemer") #-}

-- END MyRedeemer annotations
-- BEGIN interface types

type MyDatum = Integer

data MyRedeemer = R1 | R2

data MyParams = MkMyParams
  { myBool    :: Bool
  , myInteger :: Integer
  }

$(makeLift ''MyParams)

-- END interface types
-- BEGIN makeIsDataSchemaIndexed MyParams

$(makeIsDataSchemaIndexed ''MyParams [('MkMyParams, 0)])
$(makeIsDataSchemaIndexed ''MyRedeemer [('R1, 0), ('R2, 1)])

-- END makeIsDataSchemaIndexed MyParams
-- BEGIN generic instances

deriving stock instance (Generic MyParams)
deriving stock instance (Generic MyRedeemer)

-- END generic instances
-- BEGIN AsDefinitionId instances

deriving anyclass instance (AsDefinitionId MyParams)
deriving anyclass instance (AsDefinitionId MyRedeemer)

-- END AsDefinitionId instances
-- BEGIN validator

typedValidator :: MyParams -> MyDatum -> MyRedeemer -> ScriptContext -> Bool
typedValidator MkMyParams{..} datum redeemer _scriptContext =
  case redeemer of
    R1 -> myBool
    R2 -> myInteger == datum

untypedValidator :: MyParams -> BuiltinData -> BuiltinData -> BuiltinData -> ()
untypedValidator params datum redeemer scriptContext =
  check $ typedValidator params datum' redeemer' scriptContext'
 where
  datum' = unsafeFromBuiltinData datum
  redeemer' = unsafeFromBuiltinData redeemer
  scriptContext' = unsafeFromBuiltinData scriptContext

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
    , validatorCompiledCode = Nothing -- you can optionally provide the compiled code here
    }

-- END validator blueprint declaration
-- BEGIN write blueprint to file

-- >>> writeBlueprintToFile "plutus.json"
writeBlueprintToFile :: FilePath -> IO ()
writeBlueprintToFile path = writeBlueprint path myContractBlueprint

-- END write blueprint to file

