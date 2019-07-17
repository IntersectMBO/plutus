{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
module Deploy.Types where

import           Control.Newtype.Generics (Newtype, unpack)
import           Data.Aeson               (FromJSON, parseJSON, withObject, (.:))
import           Data.Text                (Text)
import qualified Data.Text                as Text
import           GHC.Generics             (Generic)
import           Options.Generic          (ParseField, ParseFields, ParseRecord)

newtype WebhookKey = WebhookKey Text
    deriving (Generic, Newtype)

data Options = Options
    { port           :: Int
    , configDir      :: FilePath
    , stateFile      :: FilePath
    , include        :: [String]
    , keyfile        :: FilePath
    , deploymentName :: Deployment
    , environment    :: String
    , ref            :: Ref
    , githubToken    :: GithubAuthorizationToken
    } deriving (Generic, Show, ParseRecord)

newtype Secrets = Secrets
    { githubWebhookKey :: WebhookKey
    }

instance FromJSON Secrets where
    parseJSON =
        withObject "Secrets" $ \v -> do
            githubWebhookKey <- WebhookKey <$> v .: "githubWebhookKey"
            pure Secrets{..}

newtype Deployment = Deployment Text
    deriving stock (Generic)
    deriving anyclass (Newtype, ParseFields, ParseRecord, ParseField)

instance Read Deployment where
    readsPrec _ s = [(Deployment . Text.pack $ s, "")]

instance Show Deployment where
    show = Text.unpack . unpack

newtype Ref = Ref Text
    deriving stock (Generic)
    deriving anyclass (Newtype, ParseFields, ParseRecord, ParseField)

instance Read Ref where
    readsPrec _ s = [(Ref . Text.pack $ s, "")]

instance Show Ref where
    show = Text.unpack . unpack

newtype GithubAuthorizationToken = GithubAuthorizationToken Text
    deriving stock (Generic)
    deriving anyclass (Newtype, ParseFields, ParseRecord, ParseField)

instance Read GithubAuthorizationToken where
    readsPrec _ s = [(GithubAuthorizationToken . Text.pack $ s, "")]

instance Show GithubAuthorizationToken where
    show = Text.unpack . unpack
