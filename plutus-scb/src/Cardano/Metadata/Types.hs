{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}

module Cardano.Metadata.Types where

import           Control.Lens              (makeLenses)
import           Control.Monad.Freer.TH    (makeEffect)
import           Data.Aeson                (FromJSON, ToJSON, toJSON, withText)
import qualified Data.Aeson                as JSON
import           Data.Aeson.Extras         (encodeByteString)
import qualified Data.ByteString.Lazy      as BSL
import           Data.List.NonEmpty        (NonEmpty)
import           Data.Text                 (Text)
import qualified Data.Text                 as Text
import           Data.Text.Extras          (tshow)
import           Data.Text.Prettyprint.Doc (Pretty, pretty, viaShow, (<+>))
import           GHC.Generics              (Generic)
import           Ledger.Crypto             (PubKey, PubKeyHash, Signature, getPubKey, getPubKeyHash)
import           LedgerBytes               (LedgerBytes)
import qualified LedgerBytes
import           Servant.API               (FromHttpApiData, ToHttpApiData)
import           Servant.Client            (BaseUrl)

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
    deriving newtype (ToJSON, FromJSON, FromHttpApiData, ToHttpApiData, Pretty)

class ToSubject a where
    toSubject :: a -> Subject

instance ToSubject BSL.ByteString where
    toSubject x = Subject $ encodeByteString $ BSL.toStrict x

instance ToSubject LedgerBytes where
    toSubject = toSubject . LedgerBytes.bytes

instance ToSubject PubKey where
    toSubject = toSubject . getPubKey

instance ToSubject PubKeyHash where
    toSubject = toSubject . getPubKeyHash

------------------------------------------------------------
newtype PropertyKey =
    PropertyKey Text
    deriving (Show, Eq, Ord, Generic)
    deriving newtype (ToJSON, FromJSON, FromHttpApiData, ToHttpApiData, Pretty)

newtype PropertyName =
    PropertyName Text
    deriving (Show, Eq, Generic)
    deriving newtype (ToJSON, FromJSON, Pretty)

data Property =
    Property
        { _propertySubject     :: Subject
        , _propertyDescription :: PropertyDescription
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty Property where
    pretty = viaShow

data HashFunction =
    SHA256
    deriving (Show, Eq, Ord, Generic)

instance FromJSON HashFunction where
    parseJSON =
        withText "HashFunction" $ \case
            "SHA256" -> pure SHA256
            other -> fail $ "Unknown HashFunction '" <> Text.unpack other <> "'"

instance ToJSON HashFunction where
    toJSON = JSON.String . tshow

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

------------------------------------------------------------
data MetadataEffect r where
    GetProperties :: Subject -> MetadataEffect [Property]
    GetProperty :: Subject -> PropertyKey -> MetadataEffect Property

makeEffect ''MetadataEffect

------------------------------------------------------------
data MetadataError
    = SubjectNotFound Subject
    | PropertyNotFound Subject PropertyKey
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON,FromJSON)

data MetadataLogMessage
    = FetchingSubject Subject
    | FetchingProperty Subject PropertyKey

instance Pretty MetadataLogMessage where
    pretty =
        \case
            FetchingSubject subject -> "Fetching subject:" <+> pretty subject
            FetchingProperty subject propertyKey ->
                "Fetching property:" <+>
                pretty subject <> "/" <> pretty propertyKey
