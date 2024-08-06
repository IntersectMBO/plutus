{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

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
import PlutusTx.Builtins.Internal (BuiltinByteString, BuiltinData, BuiltinList, BuiltinString)

-- | A reference to a Schema definition.
newtype DefinitionId = MkDefinitionId {definitionIdToText :: Text}
  deriving stock (Show, Generic, Data)
  deriving newtype (Eq, Ord, ToJSON, ToJSONKey)

class AsDefinitionId a where
  definitionId :: DefinitionId

  -- | Derive a 'DefinitionId' for a type.
  default definitionId :: (Typeable a) => DefinitionId
  definitionId =
    MkDefinitionId . Text.replace " " "_" . Text.pack . show $ typeRep (Proxy :: Proxy a)

instance AsDefinitionId () where
  definitionId = MkDefinitionId "Unit"

instance AsDefinitionId Bool

instance AsDefinitionId Integer

instance AsDefinitionId BuiltinData where
  definitionId = MkDefinitionId "Data"

instance AsDefinitionId BuiltinString where
  definitionId = MkDefinitionId "String"

instance AsDefinitionId BuiltinByteString where
  definitionId = MkDefinitionId "ByteString"

instance (AsDefinitionId a) => AsDefinitionId (BuiltinList a) where
  definitionId = MkDefinitionId $ "List_" <> definitionIdToText (definitionId @a)
