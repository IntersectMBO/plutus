{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-| CIP-0057 gives each field object an optional @title@ and identifies a
constructor by its own. These tests pin both, at the two layers that can get
them wrong: the JSON encoding of a hand-built schema, and what the Template
Haskell derivation puts there.

The fixtures precede 'tests' because each @makeIsDataSchemaIndexed@ splice ends
a declaration group; a type declared after a splice is not in scope above it. -}
module Blueprint.FieldNames.Spec (tests) where

import Prelude

import Data.Aeson (Value, toJSON)
import Data.Aeson qualified as Aeson
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Text qualified as Text
import GHC.Generics (Generic)
import PlutusTx.Blueprint.Class (HasBlueprintSchema (schema))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition, definitionRef)
import PlutusTx.Blueprint.Schema
  ( ConstructorSchema (..)
  , FieldSchema (..)
  , Schema (..)
  , emptyBytesSchema
  )
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo)
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

----------------------------------------------------------------------------------------------------
-- Fixtures ----------------------------------------------------------------------------------------

-- | A record, so its fields have names to report.
data Escrow = MkEscrow
  { escrowOwner :: Integer
  , escrowDeadline :: Integer
  }
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

$(makeIsDataSchemaIndexed ''Escrow [('MkEscrow, 0)])

-- | A positional constructor, so its fields have none.
data Pair = MkPair Integer Integer
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

$(makeIsDataSchemaIndexed ''Pair [('MkPair, 0)])

-- | Two constructors, so their titles must distinguish them.
data Outcome = Accepted | Rejected
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

$(makeIsDataSchemaIndexed ''Outcome [('Accepted, 0), ('Rejected, 1)])

----------------------------------------------------------------------------------------------------
-- Tests -------------------------------------------------------------------------------------------

tests :: TestTree
tests =
  testGroup
    "field names"
    [ testCase "a named field carries its name as title" $
        toJSON (namedCtor :: Schema '[])
          @?= Aeson.object
            [ "dataType" Aeson..= ("constructor" :: String)
            , "index" Aeson..= (0 :: Int)
            , "fields"
                Aeson..= [ Aeson.object
                             [ "title" Aeson..= ("owner" :: String)
                             , "dataType" Aeson..= ("bytes" :: String)
                             ]
                         ]
            ]
    , testCase "an unnamed field emits no title" $
        fieldsOf (toJSON (positionalCtor :: Schema '[]))
          @?= Just [Aeson.object ["dataType" Aeson..= ("bytes" :: String)]]
    , testCase "a derived record's fields carry their Haskell names" $
        (fmap titleOf <$> fieldsOf (toJSON (schema @Escrow @'[Escrow, Integer])))
          @?= Just [Just "escrowOwner", Just "escrowDeadline"]
    , testCase "a derived positional constructor's fields carry no names" $
        (fmap titleOf <$> fieldsOf (toJSON (schema @Pair @'[Pair, Integer])))
          @?= Just [Nothing, Nothing]
    , testCase "each variant of a sum type is titled with its own name" $
        variantTitles (toJSON (schema @Outcome @'[Outcome]))
          @?= Just [Just "Accepted", Just "Rejected"]
    , testCase "a single-constructor type carries no constructor title" $
        titleOf (toJSON (schema @Escrow @'[Escrow, Integer])) @?= Nothing
    ]

-- | @{ "title": "owner", "dataType": "bytes" }@ — a record field.
namedCtor :: Schema referencedTypes
namedCtor =
  SchemaConstructor
    emptySchemaInfo
    (MkConstructorSchema 0 [MkFieldSchema (Just "owner") bytes])

-- | The same constructor with a positional field.
positionalCtor :: Schema referencedTypes
positionalCtor =
  SchemaConstructor
    emptySchemaInfo
    (MkConstructorSchema 0 [MkFieldSchema Nothing bytes])

bytes :: Schema referencedTypes
bytes = SchemaBytes emptySchemaInfo emptyBytesSchema

-- | Project the @fields@ array, so a test can assert on it alone.
fieldsOf :: Value -> Maybe [Value]
fieldsOf v = case v of
  Aeson.Object o -> case KeyMap.lookup "fields" o of
    Just (Aeson.Array a) -> Just (foldr (:) [] a)
    _ -> Nothing
  _ -> Nothing

-- | The @title@ of a field or variant object, if it has one.
titleOf :: Value -> Maybe String
titleOf v = case v of
  Aeson.Object o -> case KeyMap.lookup "title" o of
    Just (Aeson.String t) -> Just (Text.unpack t)
    _ -> Nothing
  _ -> Nothing

-- | The @title@ of each variant of a @oneOf@ schema.
variantTitles :: Value -> Maybe [Maybe String]
variantTitles v = case v of
  Aeson.Object o -> case KeyMap.lookup "oneOf" o of
    Just (Aeson.Array a) -> Just (fmap titleOf (foldr (:) [] a))
    _ -> Nothing
  _ -> Nothing
