{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
module Deploy.Types where

import           Control.Newtype.Generics (Newtype, unpack)
import           Data.Aeson               (FromJSON, eitherDecodeFileStrict, parseJSON, withObject, (.:))
import           Data.Text                (Text)
import qualified Data.Text                as Text
import           GHC.Generics             (Generic)
import           Options.Generic          (ParseField, ParseFields, ParseRecord, getRecord)

newtype SlackToken = SlackToken Text
    deriving (Generic, Newtype)

newtype WebhookKey = WebhookKey Text
    deriving (Generic, Newtype)

data Options = Options
    { port           :: Int
    , configDir      :: FilePath
    , stateFile      :: FilePath
    , include        :: [String]
    , keyfile        :: FilePath
    , slackChannel   :: SlackChannel
    , deploymentName :: Deployment
    } deriving (Generic, Show, ParseRecord)

data Secrets = Secrets
    { githubWebhookKey :: WebhookKey
    , slackToken       :: SlackToken
    }

instance FromJSON Secrets where
    parseJSON =
        withObject "Secrets" $ \v -> do
            githubWebhookKey <- WebhookKey <$> v .: "githubWebhookKey"
            slackToken <- SlackToken <$> v .: "slackToken"
            pure Secrets{..}

newtype SlackChannel = SlackChannel Text
            deriving stock (Generic)
            deriving anyclass (Newtype, ParseFields, ParseRecord, ParseField)

instance Read SlackChannel where
    readsPrec _ s = [(SlackChannel . Text.pack $ s, "")]

instance Show SlackChannel where
    show = Text.unpack . unpack

newtype Deployment = Deployment Text
    deriving stock (Generic)
    deriving anyclass (Newtype, ParseFields, ParseRecord, ParseField)

instance Read Deployment where
    readsPrec _ s = [(Deployment . Text.pack $ s, "")]

instance Show Deployment where
    show = Text.unpack . unpack

