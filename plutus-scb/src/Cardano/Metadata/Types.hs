{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE RoleAnnotations   #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}

module Cardano.Metadata.Types where

import           Control.Applicative       (Alternative, (<|>))
import           Control.Monad.Freer.TH    (makeEffect)
import           Data.Aeson                (FromJSON, FromJSONKey, ToJSON, ToJSONKey, parseJSON, toJSON, withObject,
                                            withText, (.:))
import qualified Data.Aeson                as JSON
import           Data.Aeson.Extras         (decodeByteString, encodeByteString)
import           Data.Aeson.Types          (Parser)
import qualified Data.ByteString           as BS
import           Data.List.NonEmpty        (NonEmpty)
import           Data.Text                 (Text)
import qualified Data.Text                 as Text
import           Data.Text.Encoding        (encodeUtf8)
import           Data.Text.Prettyprint.Doc (Pretty, pretty, (<+>))
import           GHC.Generics              (Generic)
import           Ledger.Crypto             (PubKey (PubKey), PubKeyHash, Signature (Signature), getPubKey,
                                            getPubKeyHash)
import           LedgerBytes               (LedgerBytes)
import qualified LedgerBytes
import           Plutus.SCB.Instances      ()
import           Servant.API               (FromHttpApiData, ToHttpApiData)
import           Servant.Client            (BaseUrl, ClientError)

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
    deriving newtype ( ToJSON
                     , FromJSON
                     , FromHttpApiData
                     , ToHttpApiData
                     , Pretty
                     , ToJSONKey
                     , FromJSONKey
                     )

class ToSubject a where
    toSubject :: a -> Subject

instance ToSubject BS.ByteString where
    toSubject x = Subject $ encodeByteString x

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

type role SubjectProperties phantom

data SubjectProperties (encoding :: k) =
    SubjectProperties Subject [PropertyDescription encoding]
    deriving (Show, Eq, Generic)

deriving anyclass instance ToJSON (SubjectProperties 'AesonEncoding)
deriving anyclass instance FromJSON (SubjectProperties 'AesonEncoding)

instance FromJSON (SubjectProperties 'ExternalEncoding) where
    parseJSON =
        withObject "SubjectProperties" $ \o -> do
            subject <- o .: "subject"
            SubjectProperties subject <$>
                accumulateSuccesses
                    [ parseName o
                    , parseDescription o
                    , parsePreimage o
                    , parseOwner o
                    ]

-- | Accumulate the results from _every_ matching parser.
accumulateSuccesses ::
       ( Alternative f
       , Applicative m
       , Monoid (m a)
       , Monoid (f (m a))
       , Foldable g
       )
    => g (f a)
    -> f (m a)
accumulateSuccesses = foldMap (\parser -> (pure <$> parser) <|> pure mempty)

parseName :: JSON.Object -> Parser (PropertyDescription 'ExternalEncoding)
parseName =
    parseAtKey
        "name"
        (\subObject -> do
             value <- subObject .: "value"
             signatures :: NonEmpty (AnnotatedSignature 'ExternalEncoding) <-
                 subObject .: "anSignatures"
             pure $ Name value signatures)

parseDescription :: JSON.Object -> Parser (PropertyDescription 'ExternalEncoding)
parseDescription =
    parseAtKey
        "description"
        (\description -> do
             value <- description .: "value"
             signatures <- description .: "anSignatures"
             pure $ Description value signatures)

parsePreimage :: JSON.Object -> Parser (PropertyDescription 'ExternalEncoding)
parsePreimage =
    parseAtKey
        "preImage"
        (\preImage -> do
             hash <- preImage .: "hashFn"
             hex <- preImage .: "hex"
             pure $ Preimage hash hex)

parseOwner :: JSON.Object -> Parser (PropertyDescription 'ExternalEncoding)
parseOwner subObject = do
    sig <- subObject .: "owner"
    pure $ Other "owner" (JSON.Object subObject) (pure sig)

parseAtKey ::
       Text -> (JSON.Object -> Parser a) -> JSON.Object -> Parser a
parseAtKey key parser o = do
    subValue <- o .: key
    withObject (Text.unpack key) parser subValue

data HashFunction
    = SHA256
    | Blake2B256
    deriving (Show, Eq, Ord, Generic, Enum, Bounded)

instance FromJSON HashFunction where
    parseJSON =
        withText "HashFunction" $ \case
            "SHA256" -> pure SHA256
            "blake2b-256" -> pure Blake2B256
            other -> fail $ "Unknown HashFunction '" <> Text.unpack other <> "'"

instance ToJSON HashFunction where
    toJSON SHA256     = JSON.String "SHA256"
    toJSON Blake2B256 = JSON.String "blake2b-256"

data AnnotatedSignature (encoding :: k) =
    AnnotatedSignature PubKey Signature
    deriving (Show, Eq, Ord, Generic)

deriving anyclass instance ToJSON (AnnotatedSignature 'AesonEncoding)
deriving anyclass instance FromJSON (AnnotatedSignature 'AesonEncoding)

instance FromJSON (AnnotatedSignature 'ExternalEncoding) where
    parseJSON =
        withObject "AnnotatedSignature" $ \o -> do
            sigRaw <- o .: "signature"
            sigBytes <- decodeByteString sigRaw
            let sig = Signature sigBytes
            pubKeyRaw :: Text <- o .: "publicKey"
            case PubKey <$> LedgerBytes.fromHex (encodeUtf8 pubKeyRaw) of
                Right pubKey -> pure $ AnnotatedSignature pubKey sig
                Left err     -> fail (show (err, pubKeyRaw))

data JSONEncoding = ExternalEncoding | AesonEncoding

data PropertyDescription (encoding :: k)
    = Preimage HashFunction LedgerBytes
    | Name Text (NonEmpty (AnnotatedSignature encoding))
    | Description Text (NonEmpty (AnnotatedSignature encoding))
    | Other Text JSON.Value (NonEmpty (AnnotatedSignature encoding))
    deriving (Show, Eq, Generic)

deriving anyclass instance ToJSON (PropertyDescription 'AesonEncoding)
deriving anyclass instance FromJSON (PropertyDescription 'AesonEncoding)

instance FromJSON (PropertyDescription 'ExternalEncoding) where
    parseJSON =
        withObject "PropertyDescription" $ \o ->
            parseName o <|> parseDescription o <|> parsePreimage o <|>
            parseOwner o

toPropertyKey :: PropertyDescription encoding -> PropertyKey
toPropertyKey (Preimage _ _)    = PropertyKey "preimage"
toPropertyKey (Name _ _)        = PropertyKey "name"
toPropertyKey (Description _ _) = PropertyKey "description"
toPropertyKey (Other name _ _)  = PropertyKey name

------------------------------------------------------------
data MetadataEffect r where
    GetProperties :: Subject -> MetadataEffect (Maybe (SubjectProperties 'AesonEncoding))
    GetProperty :: Subject -> PropertyKey -> MetadataEffect (Maybe (PropertyDescription 'AesonEncoding))

makeEffect ''MetadataEffect

------------------------------------------------------------
data MetadataError
    = MetadataClientError ClientError
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

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
