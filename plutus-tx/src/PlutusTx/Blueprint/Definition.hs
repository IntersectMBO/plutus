{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE DerivingStrategies       #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

-- | This module provides a functionality to derive and reference schema definitions.
module PlutusTx.Blueprint.Definition (
  module DefinitionId,
  Definitions (..),
  Definition (..),
  definition,
  definitionRef,
  addDefinition,
  definitionsToMap,
  HasSchemaDefinition,

  -- ** Type-level utilities
  Unroll,
  UnrollAll,
  Unrollable (..),
  deriveDefinitions,
) where

import Prelude

import Data.Kind (Constraint, Type)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import GHC.Generics (Generic (Rep), K1, M1, U1, type (:*:), type (:+:))
import GHC.TypeLits qualified as GHC
import PlutusTx.Blueprint.Class (HasSchema, schema)
import PlutusTx.Blueprint.Definition.Id as DefinitionId (AsDefinitionId (..), DefinitionId (..))
import PlutusTx.Blueprint.Schema (Schema (..))
import PlutusTx.Builtins.Internal (BuiltinByteString, BuiltinData, BuiltinList, BuiltinString,
                                   BuiltinUnit)

-- | A schema definition of a type @t@ with a list of referenced types @ts@.
data Definition t ts = MkDefinition DefinitionId (Schema ts)
  deriving stock (Show)

-- | A registry of schema definitions.
data Definitions (ts :: [Type]) where
  NoDefinitions :: Definitions '[]
  AddDefinition :: Definition t ts -> Definitions ts -> Definitions (t ': ts)

deriving stock instance Show (Definitions ts)

-- | Add a schema definition to a registry.
addDefinition :: Definitions ts -> Definition t ts -> Definitions (t ': ts)
addDefinition NoDefinitions d       = AddDefinition d NoDefinitions
addDefinition (AddDefinition t s) d = AddDefinition d (AddDefinition t s)

definitionsToMap :: Definitions ts -> (forall xs. Schema xs -> v) -> Map DefinitionId v
definitionsToMap NoDefinitions _k = Map.empty
definitionsToMap (AddDefinition (MkDefinition defId v) s) k =
  Map.insert defId (k v) (definitionsToMap s k)

-- | Construct a schema definition.
definition :: forall t ts. (AsDefinitionId t, HasSchema t ts) => Definition t ts
definition = MkDefinition (definitionId @t) (schema @t)

-- | Construct a schema that is a reference to a schema definition.
definitionRef :: forall t ts. (AsDefinitionId t, HasSchemaDefinition t ts) => Schema ts
definitionRef = SchemaDefinitionRef (definitionId @t)

----------------------------------------------------------------------------------------------------
-- Functionality to "unroll" types. -- For more context see the note ["Unrolling" types] -----------

{- Note ["Unrolling" types]

ContractBlueprint needs to be parameterized by a list of types used in
a contract's type signature (including nested types) in order to:
  a) produce a JSON-schema definition for every type used.
  b) ensure that the schema definitions are referenced in a type-safe way.

Given the following contract validator's type signature:

  typedValidator :: Redeemer -> Datum -> ScriptContext -> Bool

and the following data type definitions:

  data Redeemer = MkRedeemer MyStruct
  data MyStruct = MkMyStruct { field1 :: Integer, field2 :: Bool }
  type Datum = ()

The ContractBlueprint type should be:

  ContractBlueprint '[Redeemer, MyStruct, Integer, Bool, ()]

However, for contract blurprints authors specifying all the nested types manually is
cumbersome and error-prone. To make it easier to work with, we provide the Unroll type family
that can be used to traverse a type accumulating all types nested within it:

  Unroll Redeemer ~ '[Redeemer, MyStruct, Integer, Bool]
  UnrollAll '[Redeemer, Datum] ~ '[Redeemer, MyStruct, Integer, Bool, ()]

This way blueprint authors can specify the top-level types used in a contract and the UnrollAll
type family will take care of discovering all the nested types:

  Blueprint '[Redeemer, Datum]

  is equivalent to

  ContractBlueprint '[Redeemer, MyStruct, Integer, Bool, ()]

-}

type family UnrollAll xs :: [Type] where
  UnrollAll '[] = '[]
  UnrollAll (x ': xs) = Concat (Unroll x) (UnrollAll xs)

{- | Unroll a type into a list of all nested types (including the type itself).

  If a type doesn't have a generic representation, then this type family gets "stuck".
  The good news is that for the purpose of deriving schema definitions, we only need to
  consider types that are either end-user defined (and therefore have a generic representation) or
  built-in types that we explicitly list here as terminals in order not to get "stuck".
-}
type family Unroll (p :: Type) :: [Type] where
  Unroll Int = '[Int]
  Unroll Integer = '[Integer]
  Unroll Text = '[Text]
  Unroll BuiltinData = '[BuiltinData]
  Unroll BuiltinUnit = '[BuiltinUnit]
  Unroll BuiltinString = '[BuiltinString]
  Unroll (BuiltinList a) = Prepend (BuiltinList a) (GUnroll (Rep a))
  Unroll BuiltinByteString = '[BuiltinByteString]
  Unroll p = Prepend p (GUnroll (Break (NoGeneric p) (Rep p)))

-- | Detect stuck type family: https://blog.csongor.co.uk/report-stuck-families/#custom-type-errors
type family Break e (rep :: Type -> Type) :: Type -> Type where
  Break _ (M1 a b c) = M1 a b c
  Break _ (f :*: g) = f :*: g
  Break _ (f :+: g) = f :+: g
  Break _ (K1 a b) = K1 a b
  Break e U1 = U1
  Break e x = e

type family NoGeneric t where
  NoGeneric x = GHC.TypeError (GHC.Text "No instance for " GHC.:<>: GHC.ShowType (Generic x))

-- | Unroll a generic representation of a type into a list of all nested types.
type family GUnroll (t :: Type -> Type) :: [Type] where
  GUnroll (M1 _ _ f) = GUnroll f
  GUnroll (f :*: g) = GUnroll f ++ GUnroll g
  GUnroll (f :+: g) = GUnroll f ++ GUnroll g
  GUnroll (K1 _ c) = Unroll c
  GUnroll U1 = '[]

-- | Insert @x@ into @xs@ unless it's already there.
type Insert :: forall k. k -> [k] -> [k]
type family Insert x xs where
  Insert x '[] = '[x]
  Insert x (x : xs) = x ': xs
  Insert x (y : xs) = y ': Insert x xs

type Prepend :: forall k. k -> [k] -> [k]
type family Prepend x xs where
  Prepend x '[] = '[x]
  Prepend x (x : xs) = x ': xs
  Prepend x (y : xs) = x ': y ': xs

-- | Concatenates two type-level lists
type Concat :: forall k. [k] -> [k] -> [k]
type family Concat (as :: [k]) (bs :: [k]) :: [k] where
  Concat '[] bs = bs
  Concat as '[] = as
  Concat (a : as) bs = a ': Concat as bs

-- | Concatenates two type-level lists removing duplicates.
type (++) :: forall k. [k] -> [k] -> [k]
type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  as ++ '[] = as
  (a : as) ++ bs = Insert a (as ++ bs)

infixr 5 ++

{- |
  A constraint that checks if a schema definition is present in a list of schema definitions.
  Gives a user-friendly error message if the schema definition is not found.
-}
type HasSchemaDefinition :: Type -> k -> Constraint
type family HasSchemaDefinition n xs where
  HasSchemaDefinition x (x ': xs) = ()
  HasSchemaDefinition x (_ ': xs) = HasSchemaDefinition x xs
  HasSchemaDefinition n xs =
    GHC.TypeError
      ( GHC.ShowType n
          GHC.:<>: GHC.Text " type was not found in the list of types having schema definitions."
      )

{- | This class and its two instances are used internally to derive
'Definitions' for a given list of types.
-}
class Unrollable ts where
  unroll :: Definitions ts

instance Unrollable '[] where
  unroll = NoDefinitions

instance (Unrollable ts, AsDefinitionId t, HasSchema t ts) => Unrollable (t : ts) where
  unroll = addDefinition (unroll @ts) (definition @t)

deriveDefinitions :: forall ts. (Unrollable (UnrollAll ts)) => Definitions (UnrollAll ts)
deriveDefinitions = unroll @(UnrollAll ts)
