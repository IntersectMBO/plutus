{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module PlutusTx.Blueprint.Definition.Derive where

import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition.Internal (Definition (..), Definitions (..), addDefinition)
import PlutusTx.Blueprint.Definition.Unroll (HasBlueprintDefinition (definitionId), UnrollAll)
import PlutusTx.Blueprint.Schema (Schema (..))

-- | Derive a 'Definitions' value for a list of types.
deriveDefinitions :: forall ts. DefinitionsFor (UnrollAll ts) => Definitions (UnrollAll ts)
deriveDefinitions = definitionsFor @(UnrollAll ts)

-- | Construct a 'Schema' that is a reference to a schema definition.
definitionRef :: forall t ts. HasBlueprintDefinition t => Schema ts
definitionRef = SchemaDefinitionRef (definitionId @t)

{-| This class and its two instances are used internally to derive 'Definitions'
for a given list of types. -}
type DefinitionsFor ts = DefinitionsFor' ts ts

definitionsFor :: forall ts. DefinitionsFor ts => Definitions ts
definitionsFor = definitionsFor' @ts @ts

class DefinitionsFor' referencedTypes acc where
  definitionsFor' :: Definitions referencedTypes

instance DefinitionsFor' referencedTypes '[] where
  definitionsFor' = NoDefinitions

instance
  ( HasBlueprintDefinition t
  , HasBlueprintSchema t referencedTypes
  , DefinitionsFor' referencedTypes ts
  )
  => DefinitionsFor' referencedTypes (t ': ts)
  where
  definitionsFor' =
    addDefinition
      (definitionsFor' @referencedTypes @ts)
      (MkDefinition (definitionId @t) (schema @t))
