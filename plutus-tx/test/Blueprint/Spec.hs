{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Blueprint.Spec where

import Prelude

import Data.Aeson (object, toJSON, (.=))
import Data.Kind (Type)
import Data.Typeable (Typeable, (:~:) (Refl))
import GHC.Generics (Generic)
import Language.Haskell.TH qualified as TH
import PlutusCore.Data (Data (..))
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition
  ( Definitions
  , HasBlueprintDefinition
  , UnrollAll
  , Unrolled
  , definitionRef
  , definitionsFor
  )
import PlutusTx.Blueprint.Definition.Id (definitionIdFromTypeK)
import PlutusTx.Blueprint.Definition.Unroll (definitionId)
import PlutusTx.Blueprint.Schema (Schema (..), withSchemaInfo)
import PlutusTx.Blueprint.Schema.Annotation (SchemaInfo (..), emptySchemaInfo)
import PlutusTx.Blueprint.TH qualified as PlutusTx
import PlutusTx.Builtins (BuiltinByteString)
import PlutusTx.Builtins.Internal (BuiltinData, BuiltinList, BuiltinPair, BuiltinUnit)
import PlutusTx.IsData ()
import PlutusTx.IsData.Class qualified as PlutusTx
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

data ConstructorProduct = ConstructorProduct Integer BuiltinByteString
  deriving stock (Eq, Show, Generic)
  deriving anyclass (HasBlueprintDefinition)

PlutusTx.makeIsDataSchemaIndexed ''ConstructorProduct [('ConstructorProduct, 0)]

data EmptyConstructorProduct = EmptyConstructorProduct
  deriving stock (Eq, Show, Generic)
  deriving anyclass (HasBlueprintDefinition)

PlutusTx.makeIsDataSchemaIndexed ''EmptyConstructorProduct [('EmptyConstructorProduct, 0)]

data ListProduct = ListProduct Integer BuiltinByteString
  deriving stock (Eq, Show, Generic)
  deriving anyclass (HasBlueprintDefinition)

PlutusTx.makeIsDataSchemaAsList ''ListProduct

data EmptyProduct = EmptyProduct
  deriving stock (Eq, Show, Generic)
  deriving anyclass (HasBlueprintDefinition)

PlutusTx.makeIsDataSchemaAsList ''EmptyProduct

data SumProduct = SumFirst | SumSecond

tests :: TestTree
tests =
  testGroup
    "Product schemas"
    [ testCase "constructor codec roundtrip" $ do
        let value = ConstructorProduct 3 "token"
        PlutusTx.toData value @?= Constr 0 [I 3, B "token"]
        PlutusTx.fromData (PlutusTx.toData value) @?= Just value
        PlutusTx.unsafeFromBuiltinData (PlutusTx.toBuiltinData value) @?= value
    , testCase "reject malformed constructor products" $ do
        let malformed =
              [ List [I 3, B "token"]
              , Constr 0 []
              , Constr 0 [I 3]
              , Constr 0 [I 3, I 4]
              , Constr 0 [I 3, B "token", I 4]
              , Constr 0 [I 3, B "token", I 4, B "extra"]
              ]
        map (PlutusTx.fromData @ConstructorProduct) malformed
          @?= replicate (length malformed) Nothing
    , testCase "empty constructor product" $ do
        PlutusTx.toData EmptyConstructorProduct @?= Constr 0 []
        PlutusTx.fromData @EmptyConstructorProduct (Constr 0 []) @?= Just EmptyConstructorProduct
        PlutusTx.fromData @EmptyConstructorProduct (Constr 0 [I 1]) @?= Nothing
        PlutusTx.fromData @EmptyConstructorProduct (Constr 0 [I 1, I 2]) @?= Nothing
    , testCase "list codec roundtrip" $ do
        let value = ListProduct 3 "token"
        PlutusTx.toData value @?= List [I 3, B "token"]
        PlutusTx.fromData (PlutusTx.toData value) @?= Just value
        PlutusTx.unsafeFromBuiltinData (PlutusTx.toBuiltinData value) @?= value
    , testCase "reject malformed list products" $ do
        let malformed =
              [ Constr 0 [I 3, B "token"]
              , List []
              , List [I 3]
              , List [I 3, I 4]
              , List [I 3, B "token", I 4]
              , List [I 3, B "token", I 4, B "extra"]
              ]
        map (PlutusTx.fromData @ListProduct) malformed @?= replicate (length malformed) Nothing
    , testCase "empty list product" $ do
        PlutusTx.toData EmptyProduct @?= List []
        PlutusTx.fromData @EmptyProduct (List []) @?= Just EmptyProduct
        PlutusTx.fromData @EmptyProduct (List [I 1]) @?= Nothing
        PlutusTx.fromData @EmptyProduct (List [I 1, I 2]) @?= Nothing
        schema @EmptyProduct @'[] @?= SchemaListTuple emptySchemaInfo []
    , testCase "positional schema" $
        schema @ListProduct @'[Integer, BuiltinByteString]
          @?= SchemaListTuple
            emptySchemaInfo
            [ definitionRef @Integer @'[Integer, BuiltinByteString]
            , definitionRef @BuiltinByteString @'[Integer, BuiltinByteString]
            ]
    , testCase "positional JSON and metadata" $ do
        let fields = [schema @Integer @'[], schema @BuiltinByteString @'[]]
            listSchema = withSchemaInfo (\info -> info {title = Just "Product"}) (SchemaListTuple emptySchemaInfo fields)
        toJSON listSchema
          @?= object ["dataType" .= ("list" :: String), "title" .= ("Product" :: String), "items" .= fields]
    , testCase "reject sum schema" $
        $(TH.recover [|True|] (PlutusTx.makeIsDataSchemaAsList ''SumProduct >> [|False|])) @?= True
    , testCase "reject asDataAsList sum" $
        $( TH.recover
             [|True|]
             (PlutusTx.asDataAsList [d|data RejectedSum = RejectedFirst | RejectedSecond|] >> [|False|])
         )
          @?= True
    ]

----------------------------------------------------------------------------------------------------
-- Test fixture ------------------------------------------------------------------------------------

newtype Foo = MkFoo Bar
deriving stock instance Generic Foo
deriving anyclass instance HasBlueprintDefinition Foo
instance HasBlueprintSchema Foo ts where
  schema = SchemaBuiltInUnit emptySchemaInfo

data Bar = MkBar Baz Zap
deriving stock instance Generic Bar
deriving anyclass instance HasBlueprintDefinition Bar
instance HasBlueprintSchema Bar ts where
  schema = SchemaBuiltInUnit emptySchemaInfo

data Baz = MkBaz Integer Integer
deriving stock instance Generic Baz
deriving anyclass instance HasBlueprintDefinition Baz
instance HasBlueprintSchema Baz ts where
  schema = SchemaBuiltInUnit emptySchemaInfo

data Zap = MkZap Bool Integer Nop
deriving stock instance Generic Zap
deriving anyclass instance HasBlueprintDefinition Zap
instance HasBlueprintSchema Zap ts where
  schema = SchemaBuiltInUnit emptySchemaInfo

data Nop = MkNop
deriving stock instance Generic Nop
deriving anyclass instance HasBlueprintDefinition Nop
instance HasBlueprintSchema Nop ts where
  schema = SchemaBuiltInUnit emptySchemaInfo

type Phantom :: forall k. k -> Type
data Phantom p = MkPhantom

deriving stock instance Generic (Phantom p)
instance Typeable p => HasBlueprintDefinition (Phantom (p :: k)) where
  definitionId =
    definitionIdFromTypeK @(Type -> Type) @Phantom
      <> definitionIdFromTypeK @k @p

$( PlutusTx.asData
     [d|
       data Dat = MkDat {datInteger :: Integer, datBool :: Bool}
         deriving stock (Generic)
         deriving anyclass (HasBlueprintDefinition)
       |]
 )

----------------------------------------------------------------------------------------------------
-- Tests -------------------------------------------------------------------------------------------

testUnrollBool :: Unrolled Bool :~: '[Bool]
testUnrollBool = Refl

testUnrollNop :: Unrolled Nop :~: '[Nop]
testUnrollNop = Refl

testUnrollBaz :: Unrolled Baz :~: [Baz, Integer]
testUnrollBaz = Refl

testUnrollListBaz :: Unrolled [Baz] :~: [[Baz], Integer, Baz]
testUnrollListBaz = Refl

testUnrollZap :: Unrolled Zap :~: [Zap, Bool, Integer, Nop]
testUnrollZap = Refl

testUnrollBar :: Unrolled Bar :~: [Bar, Baz, Nop, Integer, Bool, Zap]
testUnrollBar = Refl

testUnrollFoo :: Unrolled Foo :~: [Foo, Zap, Bool, Integer, Nop, Baz, Bar]
testUnrollFoo = Refl

testUnrollAll :: UnrollAll [Nop, Baz] :~: [Nop, Baz, Integer]
testUnrollAll = Refl

testUnrollDat :: Unrolled Dat :~: [Dat, BuiltinData]
testUnrollDat = Refl

testUnrollList :: Unrolled [Bool] :~: [[Bool], Bool]
testUnrollList = Refl

testUnrollNestedLists :: Unrolled [[[Bool]]] :~: [[[[Bool]]], [Bool], Bool, [[Bool]]]
testUnrollNestedLists = Refl

testUnrollPair :: Unrolled (Integer, Bool) :~: [(Integer, Bool), Integer, Bool]
testUnrollPair = Refl

testUnrollBuiltinPair
  :: Unrolled (BuiltinPair Integer Bool)
    :~: [ BuiltinPair Integer Bool
        , Integer
        , Bool
        ]
testUnrollBuiltinPair = Refl

testUnrollMaybe :: Unrolled (Maybe Bool) :~: [Maybe Bool, Bool]
testUnrollMaybe = Refl

testPhantom :: Unrolled (Phantom Bool) :~: '[Phantom Bool]
testPhantom = Refl

testUnrollBuiltinList
  :: Unrolled (BuiltinList (BuiltinPair Bool BuiltinUnit))
    :~: [ BuiltinList (BuiltinPair Bool BuiltinUnit)
        , BuiltinUnit
        , Bool
        , BuiltinPair Bool BuiltinUnit
        ]
testUnrollBuiltinList = Refl

definitions :: Definitions [Foo, Zap, Bool, Integer, Nop, Baz, Bar]
definitions = definitionsFor @(UnrollAll '[Foo])
