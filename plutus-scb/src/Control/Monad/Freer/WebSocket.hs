{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeOperators    #-}

module Control.Monad.Freer.WebSocket where

import           Control.Monad.Freer           (Eff, LastMember, interpret, type (~>))
import           Control.Monad.Freer.TH        (makeEffect)
import           Control.Monad.IO.Class        (MonadIO, liftIO)
import           Data.Aeson                    (FromJSON, ToJSON)
import qualified Data.Aeson                    as JSON
import           Data.Bifunctor                (first)
import           Data.Text                     (Text)
import qualified Data.Text                     as Text
import           Data.UUID                     (UUID)
import           Data.UUID.V4                  (nextRandom)
import qualified Network.WebSockets            as WS
import           Network.WebSockets.Connection (Connection, PendingConnection, receiveData)

data WebSocketEffect r where
    AcceptConnection :: PendingConnection -> WebSocketEffect (UUID, Connection)
    ReceiveJSON :: FromJSON a => Connection -> WebSocketEffect (Either Text a)
    SendJSON :: ToJSON a => Connection -> a -> WebSocketEffect ()

makeEffect ''WebSocketEffect

handleWebSocket ::
       forall effs m. (LastMember m effs, MonadIO m)
    => Eff (WebSocketEffect ': effs) ~> Eff effs
handleWebSocket =
    interpret $ \eff ->
        liftIO $
        case eff of
            AcceptConnection pendingConnection -> do
                connection <- WS.acceptRequest pendingConnection
                uuid <- nextRandom
                pure (uuid, connection)
            ReceiveJSON connection -> do
                msg <- receiveData connection
                pure $ first Text.pack $ JSON.eitherDecode msg
            SendJSON connection value ->
                WS.sendTextData connection $ JSON.encode value
