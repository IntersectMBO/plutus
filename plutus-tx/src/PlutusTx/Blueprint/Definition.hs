{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module PlutusTx.Blueprint.Definition where

import Prelude

import Data.Aeson (ToJSON, ToJSONKey)
import Data.Kind (Type)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Typeable (Proxy (..), Typeable, typeRep)
import PlutusTx.Blueprint.Class (HasDataSchema, dataSchema)
import PlutusTx.Blueprint.Schema (Schema)

-- | A reference to a Schema definition.
newtype DefinitionId = MkDefinitionId Text
  deriving stock (Show)
  deriving newtype (Eq, Ord, ToJSON, ToJSONKey)

definitionId :: forall a. (Typeable a) => DefinitionId
definitionId = MkDefinitionId . Text.pack . show $ typeRep (Proxy @a)

deriveSchemaDefinitions :: forall ts. (SchemaDefEntries ts) => Map DefinitionId Schema
deriveSchemaDefinitions = Map.fromList (schemaDefinitions @ts)

class SchemaDefEntries (ts :: [Type]) where schemaDefinitions :: [(DefinitionId, Schema)]

instance SchemaDefEntries '[] where schemaDefinitions = []

instance (Typeable t, HasDataSchema t ts, SchemaDefEntries ts) => SchemaDefEntries (t ': ts) where
  schemaDefinitions = (definitionId @t, dataSchema @t @ts) : schemaDefinitions @ts
