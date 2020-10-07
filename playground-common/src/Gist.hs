{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLists       #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
module Gist
    ( API
    , GistAPI
    , getGists
    , createNewGist
    , getGist
    , updateGist
    , Owner(..)
    , GistId(..)
    , Gist(..)
    , GistFile(..)
    , NewGist(..)
    , NewGistFile(..)
    ) where

import           Auth.Types        (Token, TokenProvider (Github))
import           Data.Aeson        (FromJSON, GFromJSON, ToJSON, Value, Zero, genericParseJSON, object, parseJSON,
<<<<<<< HEAD
                                    toJSON, withObject, (.!=), (.:), (.:?), (.=))
=======
                                    toJSON, withObject, (.:), (.:?), (.=), (.!=))
>>>>>>> Save entire workspace when saving to gist
import           Data.Aeson.Casing (aesonPrefix, snakeCase)
import           Data.Aeson.Types  (Parser)
import           Data.Bifunctor    (bimap)
import           Data.Map          (Map)
import           Data.Proxy        (Proxy (Proxy))
import           Data.Text         (Text)
import qualified Data.Text         as T
import           GHC.Generics      (Generic, Rep)
import           Servant.API       ((:<|>), (:>), Capture, FromHttpApiData (parseQueryParam), Get, Header, JSON, Patch,
                                    Post, ReqBody, ToHttpApiData (toQueryParam))
import           Servant.Client    (ClientM, client)
import qualified Servant.Extra
import           Text.Read         (readEither)

type API = Header "Authorization" (Token 'Github) :> "gists" :> GistAPI

type GistAPI
     = Get '[ JSON] [Gist]
       :<|> ReqBody '[ JSON] NewGist :> Post '[ JSON] Gist
       :<|> Capture "GistId" GistId :> Get '[ JSON] Gist
       :<|> Capture "GistId" GistId :> ReqBody '[ JSON] NewGist :> Patch '[ JSON] Gist

apiClient ::
       Maybe (Token 'Github)
    -> ClientM [Gist]
       :<|> (NewGist -> ClientM Gist)
       :<|> (GistId -> ClientM Gist)
       :<|> (GistId -> NewGist -> ClientM Gist)
apiClient = client (Proxy @API)

getGists :: Maybe (Token 'Github) -> ClientM [Gist]
getGists = Servant.Extra.left . apiClient

createNewGist :: Maybe (Token 'Github) -> NewGist -> ClientM Gist
createNewGist = Servant.Extra.left . Servant.Extra.right . apiClient

getGist :: Maybe (Token 'Github) -> GistId -> ClientM Gist
getGist =
    Servant.Extra.left . Servant.Extra.right . Servant.Extra.right . apiClient

updateGist :: Maybe (Token 'Github) -> GistId -> NewGist -> ClientM Gist
updateGist =
    Servant.Extra.right . Servant.Extra.right . Servant.Extra.right . apiClient

------------------------------------------------------------
data Owner =
    Owner
        { _ownerLogin   :: !Text
        , _ownerHtmlUrl :: !Text
        }
    deriving (Show, Eq, Generic, ToJSON)

instance FromJSON Owner where
    parseJSON = githubParseJSON

data NewGist =
    NewGist
        { _newGistDescription :: !Text
        , _newGistPublic      :: !Bool
        , _newGistFiles       :: ![NewGistFile]
        }
    deriving (Show, Eq, Generic, FromJSON)

instance ToJSON NewGist where
    toJSON NewGist {..} =
        object
            [ "description" .= _newGistDescription
            , "public" .= _newGistPublic
            , "files" .= object (toPair <$> _newGistFiles)
            ]
      where
        toPair NewGistFile {..} =
            (_newGistFilename, object ["content" .= _newGistFileContent])

data NewGistFile =
    NewGistFile
        { _newGistFilename    :: !Text
        , _newGistFileContent :: !Text
        }
    deriving (Show, Eq, Generic, FromJSON)

newtype GistId =
    GistId Text
    deriving (Show, Eq, Ord, Generic, FromJSON, ToJSON)

instance ToHttpApiData GistId where
    toQueryParam (GistId gistId) = gistId

instance FromHttpApiData GistId where
    parseQueryParam = bimap T.pack GistId . readEither . T.unpack

data Gist =
    Gist
        { _gistId          :: !GistId
        , _gistGitPushUrl  :: !Text
        , _gistHtmlUrl     :: !Text
        , _gistOwner       :: !Owner
        , _gistFiles       :: !(Map String GistFile)
        , _gistTruncated   :: !Bool
        , _gistCreatedAt   :: !String
        , _gistUpdatedAt   :: !String
        , _gistDescription :: !String
        }
    deriving (Show, Eq, Generic, ToJSON)

instance FromJSON Gist where
    parseJSON =
        withObject "gist" $ \o -> do
            _gistId <- o .: "id"
            _gistGitPushUrl <- o .: "git_push_url"
            _gistHtmlUrl <- o .: "html_url"
            _gistOwner <- o .: "owner"
            _gistFiles <- (o .: "files")
            _gistTruncated <- o .: "truncated"
            _gistCreatedAt <- o .: "created_at"
            _gistUpdatedAt <- o .: "updated_at"
<<<<<<< HEAD
            -- playground gists will always have a description but to avoid breaking with non-playground gists we change null to empty string
=======
>>>>>>> Save entire workspace when saving to gist
            _gistDescription <- o .:? "description" .!= ""
            pure Gist {..}

data GistFile =
    GistFile
        { _gistFileFilename  :: !Text
        , _gistFileLanguage  :: !(Maybe Text)
        , _gistFileType      :: !Text
        , _gistFileTruncated :: !(Maybe Bool)
        , _gistFileContent   :: !(Maybe Text)
        }
    deriving (Show, Eq, Generic, ToJSON)

instance FromJSON GistFile where
    parseJSON =
        withObject "gistfile" $ \o -> do
            _gistFileFilename <- o .: "filename"
            _gistFileLanguage <- o .:? "language"
            _gistFileType <- o .: "type"
            _gistFileTruncated <- o .:? "truncated"
            _gistFileContent <- o .:? "content"
            pure GistFile {..}

------------------------------------------------------------
githubParseJSON :: (Generic a, GFromJSON Zero (Rep a)) => Value -> Parser a
githubParseJSON = genericParseJSON $ aesonPrefix snakeCase
