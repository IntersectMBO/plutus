{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}

module API where

import           Data.Aeson           (FromJSON, ToJSON, Value)
import qualified Data.ByteString.Lazy as BS
import           Data.Text            (Text)
import           GHC.Generics         (Generic)
import           Network.HTTP.Media   ((//), (/:))
import           Servant.API          (Accept (..), Capture, EmptyAPI, Get, Header, JSON, MimeRender (..), NoContent,
                                       PlainText, Post, Raw, ReqBody, (:<|>), (:>))

instance Accept HTML where
  contentType _ = "text" // "html" /: ("charset", "utf-8")
newtype RawHtml = RawHtml { unRaw :: BS.ByteString }

data HTML = HTML

instance MimeRender HTML RawHtml where
    mimeRender _ =  unRaw

type PrivateKey = String

type PublicKey = String

type JSON_API = "create_wallet" :> ReqBody '[JSON] PrivateKey :> Post '[JSON] PublicKey
type STATIC = Raw
type API = JSON_API :<|>
           "create_wallet" :> Capture "secret" String :> Get '[PlainText] String :<|>
           "test" :> Get '[HTML] RawHtml :<|> Raw

