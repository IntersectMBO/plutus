{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Blueprint.Spec where

import Prelude

import Data.Set qualified as Set
import GHC.Generics (Generic)
import PlutusTx.Blueprint.Class (HasSchema (..))
import PlutusTx.Blueprint.Contract (Blueprint, ContractBlueprint (..))
import PlutusTx.Blueprint.Definition (AsDefinitionId, Unroll, UnrollAll, deriveSchemaDefinitions)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (PlutusV3))
import PlutusTx.Blueprint.Preamble (Preamble (MkPreamble))
import PlutusTx.Blueprint.Schema (Schema (..))
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo)

contract :: Blueprint [Foo, Bar, Baz]
contract =
  MkContractBlueprint
    { contractId = Nothing
    , contractPreamble = MkPreamble "" Nothing "" PlutusV3 Nothing
    , contractValidators = Set.empty
    , contractDefinitions = deriveSchemaDefinitions
    }

testUnrollNop :: Unroll Nop :~: '[Nop]
testUnrollNop = Refl

testUnrollBaz :: Unroll Baz :~: [Integer, Baz]
testUnrollBaz = Refl

testUnrollZap :: Unroll Zap :~: [Nop, Integer, Bool, Zap]
testUnrollZap = Refl

testUnrollBar :: Unroll Bar :~: [Nop, Integer, Bool, Zap, Baz, Bar]
testUnrollBar = Refl

testUnrollFoo :: Unroll Foo :~: [Nop, Integer, Bool, Zap, Baz, Bar, Foo]
testUnrollFoo = Refl

testUnrollAll :: UnrollAll [Nop, Baz] :~: [Integer, Baz, Nop]
testUnrollAll = Refl

----------------------------------------------------------------------------------------------------
-- Helper types/functions --------------------------------------------------------------------------

{- | Evidence that @a@ is the same type as @b@.

  The @'Functor'@, @'Applicative'@, and @'Monad'@ instances of @Maybe@
  are very useful for working with values of type @Maybe (a :~: b)@.
-}
data a :~: b where
  Refl :: (a ~ b) => a :~: b

----------------------------------------------------------------------------------------------------
-- Test fixture ------------------------------------------------------------------------------------

newtype Foo = MkFoo Bar
deriving stock instance (Generic Foo)
deriving anyclass instance (AsDefinitionId Foo)
instance HasSchema Foo ts where
  schema = SchemaBuiltInUnit emptySchemaInfo

data Bar = MkBar Baz Zap
deriving stock instance (Generic Bar)
deriving anyclass instance (AsDefinitionId Bar)
instance HasSchema Bar ts where
  schema = SchemaBuiltInUnit emptySchemaInfo

data Baz = MkBaz Integer Integer
deriving stock instance (Generic Baz)
deriving anyclass instance (AsDefinitionId Baz)
instance HasSchema Baz ts where
  schema = SchemaBuiltInUnit emptySchemaInfo

data Zap = MkZap Bool Integer Nop
deriving stock instance (Generic Zap)
deriving anyclass instance (AsDefinitionId Zap)
instance HasSchema Zap ts where
  schema = SchemaBuiltInUnit emptySchemaInfo

data Nop = MkNop
deriving stock instance (Generic Nop)
deriving anyclass instance (AsDefinitionId Nop)
instance HasSchema Nop ts where
  schema = SchemaBuiltInUnit emptySchemaInfo
