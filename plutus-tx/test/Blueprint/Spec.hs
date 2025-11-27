{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Blueprint.Spec where

import Prelude

import Data.Kind (Type)
import Data.Typeable (Typeable, (:~:) (Refl))
import GHC.Generics (Generic)
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition
  ( Definitions
  , HasBlueprintDefinition
  , UnrollAll
  , Unrolled
  , definitionsFor
  )
import PlutusTx.Blueprint.Definition.Id (definitionIdFromTypeK)
import PlutusTx.Blueprint.Definition.Unroll (definitionId)
import PlutusTx.Blueprint.Schema (Schema (..))
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo)
import PlutusTx.Builtins.Internal (BuiltinData, BuiltinList, BuiltinPair, BuiltinUnit)
import PlutusTx.IsData ()

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
