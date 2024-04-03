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
module PlutusTx.Blueprint.Definition.Internal (
  Definitions (..),
  Definition (..),
  definition,
  definitionRef,
  addDefinition,
  definitionsToMap,
  HasSchemaDefinition,
) where

import Prelude

import Data.Kind (Constraint, Type)
import Data.Map (Map)
import Data.Map qualified as Map
import GHC.TypeLits qualified as GHC
import PlutusTx.Blueprint.Class (HasSchema, schema)
import PlutusTx.Blueprint.Definition.Id (AsDefinitionId (..), DefinitionId)
import PlutusTx.Blueprint.Schema (Schema (..))

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
