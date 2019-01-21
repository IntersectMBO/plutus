{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Gist
  ( API
  , getGists
  , Owner(..)
  , Gist(..)
  , GistFile(..)
  ) where

import           Data.Aeson        (FromJSON, GFromJSON, ToJSON, Value, Zero, genericParseJSON, parseJSON, withObject,
                                    (.:))
import           Data.Aeson.Casing (aesonPrefix, snakeCase)
import           Data.Aeson.Types  (Parser)
import           Data.Map          (Map)
import qualified Data.Map          as Map
import           Data.Proxy        (Proxy (Proxy))
import           Data.Text         (Text)
import           GHC.Generics      (Generic, Rep)
import           Servant.API       ((:>), Get, Header, JSON)
import           Servant.Client    (ClientM, client)
import           Auth.Types        (Token, TokenProvider (Github))

type API
   = Header "Authorization" (Token 'Github) :> "gists" :> Get '[ JSON] [Gist]

getGists :: Maybe (Token 'Github) -> ClientM [Gist]
getGists = client (Proxy @API)

------------------------------------------------------------
data Owner = Owner
  { _ownerLogin   :: !Text
  , _ownerHtmlUrl :: !Text
  } deriving (Show, Eq, Generic, ToJSON)

data Gist = Gist
  { _gistGitPushUrl :: !Text
  , _gistOwner      :: !Owner
  , _gistFiles      :: ![GistFile]
  , _gistTruncated  :: !Bool
  } deriving (Show, Eq, Generic, ToJSON)

data GistFile = GistFile
  { _gistFilename :: !Text
  , _gistLanguage :: !(Maybe Text)
  , _gistType     :: !Text
  } deriving (Show, Eq, Generic, ToJSON)

instance FromJSON Gist where
  parseJSON =
    withObject "gist" $ \o -> do
      _gistGitPushUrl <- o .: "git_push_url"
      _gistOwner <- o .: "owner"
      _gistFiles <-
        Map.elems <$> ((o .: "files") :: Parser (Map String GistFile))
      _gistTruncated <- o .: "truncated"
      pure Gist {..}

instance FromJSON Owner where
  parseJSON = githubParseJSON

instance FromJSON GistFile where
  parseJSON = githubParseJSON

------------------------------------------------------------
githubParseJSON :: (Generic a, GFromJSON Zero (Rep a)) => Value -> Parser a
githubParseJSON = genericParseJSON $ aesonPrefix snakeCase
