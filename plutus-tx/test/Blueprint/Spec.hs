{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Blueprint.Spec where

import Prelude

import Data.Typeable ((:~:) (Refl))
import GHC.Generics (Generic)
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Blueprint.Class (HasSchema (..))
import PlutusTx.Blueprint.Definition (AsDefinitionId, Definitions, GenericUnroll, Unroll, UnrollAll,
                                      Unrollable (..))
import PlutusTx.Blueprint.Schema (Schema (..))
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo)
import PlutusTx.IsData ()

----------------------------------------------------------------------------------------------------
-- Test fixture ------------------------------------------------------------------------------------

newtype Foo = MkFoo Bar
deriving stock instance (Generic Foo)
deriving anyclass instance (AsDefinitionId Foo)
instance HasSchema Foo ts where
  schema = SchemaBuiltInUnit emptySchemaInfo
type instance Unroll Foo = GenericUnroll Foo

data Bar = MkBar Baz Zap
deriving stock instance (Generic Bar)
deriving anyclass instance (AsDefinitionId Bar)
instance HasSchema Bar ts where
  schema = SchemaBuiltInUnit emptySchemaInfo
type instance Unroll Bar = GenericUnroll Bar

data Baz = MkBaz Integer Integer
deriving stock instance (Generic Baz)
deriving anyclass instance (AsDefinitionId Baz)
instance HasSchema Baz ts where
  schema = SchemaBuiltInUnit emptySchemaInfo
type instance Unroll Baz = GenericUnroll Baz

data Zap = MkZap Bool Integer Nop
deriving stock instance (Generic Zap)
deriving anyclass instance (AsDefinitionId Zap)
instance HasSchema Zap ts where
  schema = SchemaBuiltInUnit emptySchemaInfo
type instance Unroll Zap = GenericUnroll Zap

data Nop = MkNop
deriving stock instance (Generic Nop)
deriving anyclass instance (AsDefinitionId Nop)
instance HasSchema Nop ts where
  schema = SchemaBuiltInUnit emptySchemaInfo
type instance Unroll Nop = GenericUnroll Nop

$( PlutusTx.asData
    [d|
      data Dat = MkDat {datInteger :: Integer, datBool :: Bool}
        deriving stock (Generic)
        deriving newtype (AsDefinitionId)
      |]
 )
type instance Unroll Dat = '[Dat, Integer, Bool]

----------------------------------------------------------------------------------------------------
-- Tests -------------------------------------------------------------------------------------------

testUnrollNop :: Unroll Nop :~: '[Nop]
testUnrollNop = Refl

testUnrollBaz :: Unroll Baz :~: [Baz, Integer]
testUnrollBaz = Refl

testUnrollZap :: Unroll Zap :~: [Zap, Nop, Integer, Bool]
testUnrollZap = Refl

testUnrollBar :: Unroll Bar :~: [Bar, Zap, Nop, Integer, Bool, Baz]
testUnrollBar = Refl

testUnrollFoo :: Unroll Foo :~: [Foo, Bar, Zap, Nop, Integer, Bool, Baz]
testUnrollFoo = Refl

testUnrollAll :: UnrollAll [Nop, Baz] :~: [Nop, Baz, Integer]
testUnrollAll = Refl

definitions :: Definitions [Foo, Bar, Zap, Nop, Integer, Bool, Baz]
definitions = unroll @(UnrollAll '[Foo])

testUnrollDat :: Unroll Dat :~: '[Dat, Integer, Bool]
testUnrollDat = Refl
