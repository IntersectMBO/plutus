{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}

module PlutusTx.Blueprint.Definition.Id
  ( DefinitionId
  , definitionIdFromType
  , definitionIdFromTypeK
  , definitionIdToText
  , definitionIdUnit
  , definitionIdList
  , definitionIdTuple2
  , definitionIdTuple3
  ) where

import Prelude

import Data.Aeson (ToJSON, ToJSONKey)
import Data.Data (Data)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.Text (Text, pack)
import Data.Typeable (Typeable, typeRep)
import GHC.Generics (Generic)

-- | A reference to a Schema definition.
newtype DefinitionId = MkDefinitionId {definitionIdToText :: Text}
  deriving stock (Show, Generic, Data)
  deriving newtype (Eq, Ord, ToJSON, ToJSONKey)

instance Semigroup DefinitionId where
  (<>) l r = MkDefinitionId $ definitionIdToText l <> "_" <> definitionIdToText r

-- | Creates a 'DefinitionId' from a type with a kind 'Type'.
definitionIdFromType :: forall (t :: Type). Typeable t => DefinitionId
definitionIdFromType = MkDefinitionId . pack . show . typeRep $ Proxy @t

{-| Creates a 'DefinitionId' from a type with a kind other than 'Type'.
Example:
> definitionIdFromTypeK @(Type -> Type) @Maybe -}
definitionIdFromTypeK :: forall k (t :: k). Typeable (t :: k) => DefinitionId
definitionIdFromTypeK = MkDefinitionId . pack . show . typeRep $ Proxy @(t :: k)

-- Special cases that we want to be alphanumeric instead of symbolic,
-- E.g. "Unit" instead of "()", "List" instead of "[]" etc.

definitionIdUnit :: DefinitionId
definitionIdUnit = MkDefinitionId "Unit"

definitionIdList :: DefinitionId
definitionIdList = MkDefinitionId "List"

definitionIdTuple2 :: DefinitionId
definitionIdTuple2 = MkDefinitionId "Tuple2"

definitionIdTuple3 :: DefinitionId
definitionIdTuple3 = MkDefinitionId "Tuple3"
