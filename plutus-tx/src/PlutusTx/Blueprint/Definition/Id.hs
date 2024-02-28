{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures   #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DerivingStrategies  #-}

module PlutusTx.Blueprint.Definition.Id (
  DefinitionId,
  definitionIdToText,
  AsDefinitionId (..),
) where

import Prelude

import Data.Aeson (ToJSON, ToJSONKey)
import Data.Data (Data)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Typeable (Proxy (..), Typeable, typeRep)
import GHC.Generics (Generic)
import PlutusTx.Builtins (BuiltinByteString, BuiltinData, BuiltinString)

-- | A reference to a Schema definition.
newtype DefinitionId = MkDefinitionId Text
  deriving stock (Show, Generic, Data)
  deriving newtype (Eq, Ord, ToJSON, ToJSONKey)

definitionIdToText :: DefinitionId -> Text
definitionIdToText (MkDefinitionId t) = t

class AsDefinitionId a where
  definitionId :: DefinitionId

  -- | Derive a 'DefinitionId' for a type.
  default definitionId :: (Typeable a) => DefinitionId
  definitionId = MkDefinitionId . Text.pack . show $ typeRep (Proxy :: Proxy a)

instance AsDefinitionId () where
  definitionId = MkDefinitionId (Text.pack "Unit")
instance AsDefinitionId Bool
instance AsDefinitionId Integer
instance AsDefinitionId BuiltinData where
  definitionId = MkDefinitionId (Text.pack "Data")
instance AsDefinitionId BuiltinString where
  definitionId = MkDefinitionId (Text.pack "String")
instance AsDefinitionId BuiltinByteString where
  definitionId = MkDefinitionId (Text.pack "ByteString")
