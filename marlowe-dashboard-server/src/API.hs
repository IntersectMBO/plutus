{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeOperators      #-}

module API where

import           Data.Aeson            (FromJSON, ToJSON, Value)
import           Data.Text             (Text)
import           GHC.Generics          (Generic)
import           Servant.API           (Capture, Get, Header, JSON, NoContent, PlainText, Post, Raw, ReqBody, (:<|>),
                                        (:>))
import           Servant.API.WebSocket (WebSocketPending)

type API = WebSocketAPI :<|> Raw

type HTTPAPI = "version" :> Get '[PlainText, JSON] Text

type WebSocketAPI = "ws" :> WebSocketPending
