{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
module Cardano.Metadata.Types where

import           Control.Lens           (makeLenses)
import           Control.Monad.Freer.TH (makeEffect)
import           Data.Aeson             (FromJSON, ToJSON, toJSON)
import qualified Data.Aeson             as JSON
import           Data.List.NonEmpty     (NonEmpty)
import           Data.Text              (Text)
import           GHC.Generics           (Generic)
import           Ledger.Crypto          (PubKey, Signature)
import           LedgerBytes            (LedgerBytes)
import           Servant.API            (FromHttpApiData, ToHttpApiData)
import           Servant.Client         (BaseUrl)

newtype MetadataConfig =
    MetadataConfig
        { mdBaseUrl :: BaseUrl
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON)

------------------------------------------------------------
newtype Subject =
    Subject Text
    deriving (Show, Eq, Ord, Generic)
    deriving newtype (ToJSON, FromJSON, FromHttpApiData, ToHttpApiData)

newtype PropertyKey =
    PropertyKey Text
    deriving (Show, Eq, Ord, Generic)
    deriving newtype (ToJSON, FromJSON, FromHttpApiData, ToHttpApiData)

newtype PropertyName =
    PropertyName Text
    deriving (Show, Eq, Generic)
    deriving newtype (ToJSON, FromJSON)

data Property =
    Property
        { _propertySubject     :: Subject
        , _propertyDescription :: PropertyDescription
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

data HashFunction =
    SHA256
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

data PropertyDescription
    = Preimage HashFunction LedgerBytes
    | Name Text (NonEmpty AnnotatedSignature)
    | Description Text (NonEmpty AnnotatedSignature)
    | Other Text JSON.Value (NonEmpty AnnotatedSignature)
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

data AnnotatedSignature =
    AnnotatedSignature PubKey Signature
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeLenses ''Property

toId :: Property -> (Subject, PropertyKey)
toId (Property subject description) = (subject, toPropertyKey description)

toPropertyKey :: PropertyDescription -> PropertyKey
toPropertyKey (Preimage _ _)    = PropertyKey "preimage"
toPropertyKey (Name _ _)        = PropertyKey "name"
toPropertyKey (Description _ _) = PropertyKey "description"
toPropertyKey (Other name _ _)  = PropertyKey name

toPayload :: PropertyDescription -> JSON.Value
toPayload (Preimage _ bytes)    = toJSON bytes
toPayload (Name value _)        = toJSON value
toPayload (Description value _) = toJSON value
toPayload (Other _ value _)     = toJSON value
------------------------------------------------------------

data MetadataEffect r where
  GetProperties :: Subject -> MetadataEffect [Property]
  GetProperty :: Subject -> PropertyKey -> MetadataEffect JSON.Value

makeEffect ''MetadataEffect
