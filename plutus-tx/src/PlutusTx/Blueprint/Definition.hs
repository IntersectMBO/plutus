{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE TypeApplications    #-}

module PlutusTx.Blueprint.Definition where

import Prelude

import Data.Aeson (ToJSON, ToJSONKey)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Typeable (Proxy (..), Typeable, typeRep)
import PlutusTx.Blueprint.Class (HasDataSchema, dataSchema)
import PlutusTx.Blueprint.Schema (DataSchema)

-- | A reference to a DataSchema definition.
newtype DefinitionId = MkDefinitionId Text
  deriving stock (Show)
  deriving newtype (Eq, Ord, ToJSON, ToJSONKey)

definitionId :: forall a. (Typeable a) => DefinitionId
definitionId = MkDefinitionId . Text.pack . show $ typeRep (Proxy @a)

definitionEntry :: forall a. (Typeable a, HasDataSchema a) => (DefinitionId, DataSchema)
definitionEntry = (definitionId @a, dataSchema @a)
