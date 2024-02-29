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
  HasSchemaDefinition,
  definitionRef,
  deriveSchemaDefinitions,
) where

import Data.Kind (Constraint, Type)
import Data.Map (Map)
import Data.Map qualified as Map
import GHC.TypeLits qualified as GHC
import PlutusTx.Blueprint.Class (HasDataSchema, dataSchema)
import PlutusTx.Blueprint.Definition.Id as DefinitionId
import PlutusTx.Blueprint.Schema (Schema (..))

-- | Construct a schema that is a reference to a schema definition.
definitionRef ::
  forall typ schemas.
  (AsDefinitionId typ, HasSchemaDefinition typ schemas) =>
  Schema
definitionRef = SchemaDefinitionRef (definitionId @typ)

{- | A constraint that checks if a schema definition is present in a list of schema definitions.
| Gives a user-friendly error message if the schema definition is not found.
-}
type HasSchemaDefinition :: Type -> k -> Constraint
type family HasSchemaDefinition n xs where
  HasSchemaDefinition x (x ': xs) = ()
  HasSchemaDefinition x (_ ': xs) = HasSchemaDefinition x xs
  HasSchemaDefinition n xs =
    GHC.TypeError
      ( GHC.ShowType n
          GHC.:<>: GHC.Text " schema was not found in the list of schema definitions."
      )

-- | Derive a map of schema definitions from a list of types.
deriveSchemaDefinitions ::
  forall (ts :: [Type]).
  (AsDefinitionsEntries ts ts) =>
  Map DefinitionId Schema
deriveSchemaDefinitions = Map.fromList (definitionEntries @ts @ts)

{- | A class of types that can be converted to a list of schema definition entries.
It is used internally to derive a map of schema definitions from a list of types.
-}
class AsDefinitionsEntries (allTypes :: [Type]) (remainingTypes :: [Type]) where
  definitionEntries :: [(DefinitionId, Schema)]

instance AsDefinitionsEntries allTypes '[] where
  definitionEntries = []

instance
  ( AsDefinitionId t
  , HasDataSchema t allTypes
  , AsDefinitionsEntries allTypes ts
  ) =>
  AsDefinitionsEntries allTypes (t ': ts)
  where
  definitionEntries =
    (definitionId @t, dataSchema @t @allTypes)
      : definitionEntries @allTypes @ts
