{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
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
  Unroll,
  UnrollAll,
  HasSchemaDefinition,
  definitionRef,
  deriveSchemaDefinitions,
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

-- For more context see the note ["Unrolling" types]

type family UnrollAll xs :: [Type] where
  UnrollAll '[] = '[]
  UnrollAll (x ': xs) = Unroll x ++ UnrollAll xs

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
  Unroll (BuiltinList a) = Insert (BuiltinList a) (GUnroll (Rep a))
  Unroll BuiltinByteString = '[BuiltinByteString]
  Unroll p = Insert p (GUnroll (Break (NoGeneric p) (Rep p)))

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

-- | Concatenates two type-level lists removing duplicates.
type (++) :: forall k. [k] -> [k] -> [k]
type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  as ++ '[] = as
  (a : as) ++ bs = Insert a (as ++ bs)

infixr 5 ++

-- | Construct a schema that is a reference to a schema definition.
definitionRef ::
  forall typ types.
  (AsDefinitionId typ, HasSchemaDefinition typ types) =>
  Schema types
definitionRef = SchemaDefinitionRef (definitionId @typ)

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

-- | Derive a map of schema definitions from a list of types.
deriveSchemaDefinitions ::
  forall (types :: [Type]).
  (AsDefinitionsEntries types types) =>
  Map DefinitionId (Schema types)
deriveSchemaDefinitions = Map.fromList (definitionEntries @types @types)

{- | This class is only used internally to derive schema definition entries from a list of types.

It uses 2 instances to iterate a type-level list:
  * one instance terminates recursion when the list of [remaining] types to iterate is empty.
  * another instance does a recursive step:
      taking a head and tail,
      adds a schema definition entry if the head is in the `allTypes`
      and recurses on tail as `remainingTypes`.

This way in the beginning of iteration `allTypes` == `remainingTypes` and then
`allTypes` stays the same list, while `remainingTypes` is shrinking until empty.

Here is an analogy at the value level, where `remainingTypes` serves a similar purpose:

@
type Typ = String
type DefinitionId = String
type Schema = String

asDefinitionEntries :: [Typ] -> [(DefinitionId, Schema)]
asDefinitionEntries allTypes = go allTypes allTypes
  where
    go :: [Typ] -> [Typ] -> [(DefinitionId, Schema)]
    go allTypes remainingTypes =
      case remainingTypes of
        [] -> []
        (h : t) ->
          let defId = lookupDefinitionId h allTypes
              schema = lookupSchema h allTypes
          in (defId, schema) : go allTypes t

lookupDefinitionId :: Typ -> [Typ] -> DefinitionId
lookupDefinitionId t allTypes | t `elem` allTypes = "DefinitionId for " ++ t
lookupDefinitionId t _ = error $ "Type " ++ show t ++ " not found"

lookupSchema :: Typ -> [Typ] -> Schema
lookupSchema t allTypes | t `elem` allTypes = "Schema for " ++ t
lookupSchema t _ = error $ "Type " ++ show t ++ " not found"
@
-}
class AsDefinitionsEntries (allTypes :: [Type]) (remainingTypes :: [Type]) where
  definitionEntries :: [(DefinitionId, Schema allTypes)]

instance AsDefinitionsEntries allTypes '[] where
  definitionEntries = []

instance
  ( AsDefinitionId t
  , HasSchema t allTypes
  , AsDefinitionsEntries allTypes ts
  ) =>
  AsDefinitionsEntries allTypes (t ': ts)
  where
  definitionEntries =
    (definitionId @t, schema @t @allTypes)
      : definitionEntries @allTypes @ts
