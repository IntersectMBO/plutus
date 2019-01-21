{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Auth.Types
  ( addUserAgent
  , OAuthCode(OAuthCode)
  , OAuthToken(..)
  , TokenProvider(..)
  , Token(..)
  ) where

import           Control.Newtype.Generics (Newtype)
import           Data.Aeson               (FromJSON, ToJSON, genericParseJSON, parseJSON)
import           Data.Aeson.Casing        (aesonDrop, snakeCase)
import           Data.Text                (Text)
import           GHC.Generics             (Generic)
import           Network.HTTP.Conduit     (Request)
import           Network.HTTP.Simple      (addRequestHeader)
import           Network.HTTP.Types       (hUserAgent)
import           Servant                  (FromHttpApiData, ToHttpApiData, parseQueryParam, toUrlPiece)

------------------------------------------------------------
newtype OAuthCode =
  OAuthCode Text
  deriving (Show, Eq)

instance FromHttpApiData OAuthCode where
  parseQueryParam = Right . OAuthCode

data OAuthToken a = OAuthToken
  { oAuthTokenAccessToken :: !(Token a)
  , oAuthTokenScope       :: !Text
  , oAuthTokenTokenType   :: !Text
  } deriving (Show, Eq, Generic)

-- | We use the default JSON encoding for sending-to-PureScript's
-- sake, but a custom one for receiving-from-Github.
instance ToJSON (OAuthToken a)

instance FromJSON (OAuthToken a) where
  parseJSON = genericParseJSON $ aesonDrop 10 snakeCase

------------------------------------------------------------
data TokenProvider =
  Github

newtype Token (a :: TokenProvider) =
  Token Text
  deriving stock (Show, Eq,Generic)
  deriving newtype (FromJSON,ToJSON)
  deriving anyclass (Newtype)

instance ToHttpApiData (Token a) where
  toUrlPiece (Token token) = "token " <> token

addUserAgent :: Request -> Request
addUserAgent = addRequestHeader hUserAgent "haskell-conduit"
