{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-deprecations #-}
module WebSocket where

import           Control.Concurrent.STM          (STM)
import           Control.Concurrent.STM.TVar     (TVar, newTVar)
import           Control.Exception               (SomeException, handle)
import           Control.Monad                   (forever)
import           Control.Monad.Except            (MonadError, throwError)
import           Control.Monad.IO.Class          (MonadIO, liftIO)
import           Control.Newtype.Generics        (Newtype, over, unpack)
import           Data.Aeson                      (FromJSON, ToJSON)
import           Data.Map.Strict                 (Map)
import qualified Data.Map.Strict                 as Map
import           Data.Text                       (Text)
import           Data.UUID                       (UUID)
import           Data.UUID.V4                    (nextRandom)
import           GHC.Generics                    (Generic)
import qualified Marlowe.Symbolic.Types.Response as MSRes
import           Network.WebSockets              (WebSocketsData)
import           Network.WebSockets.Connection   (Connection, PendingConnection, acceptRequest, forkPingThread,
                                                  receiveData)

data WebSocketRequestMessage
    = CheckForWarnings String String
    deriving (Generic, ToJSON, FromJSON)

data WebSocketResponseMessage
    = CheckForWarningsResult MSRes.Result
    | OtherError String
    deriving (Generic, ToJSON, FromJSON)

-- | Each Connection is allowed only 1 active request at a time
--   We model this with Maybe since we also want the @UUID@ of this request
newtype Registry = Registry (Map UUID (Connection, Maybe UUID))
    deriving (Generic, Newtype)

newRegistry :: STM (TVar Registry)
newRegistry = newTVar $ Registry Map.empty

insertIntoRegistry :: UUID -> Connection -> Registry -> Registry
insertIntoRegistry uuid connection = over Registry (Map.insert uuid (connection, Nothing))

deleteFromRegistry :: UUID -> Registry -> Registry
deleteFromRegistry uuid = over Registry (Map.delete uuid)

lookupInRegistry :: UUID -> Registry -> Maybe (Connection, Maybe UUID)
lookupInRegistry uuid = Map.lookup uuid . unpack

startWaiting :: UUID -> UUID -> Registry -> Registry
startWaiting uuid waiting = over Registry (Map.adjust (\(connection, _) -> (connection, Just waiting)) uuid)

finishWaiting :: UUID -> Registry -> Registry
finishWaiting uuid = over Registry (Map.adjust (\(connection, _) -> (connection, Nothing)) uuid)

isWaiting :: UUID -> UUID -> Registry -> Bool
isWaiting uuid waiting registry = case Map.lookup uuid (unpack registry) of
                                    Nothing                  -> False
                                    Just (_, currentWaiting) -> Just waiting == currentWaiting

-- | Take a @PendingConnection@ and returns a @UUID@ and @Connection$ for the user
initializeConnection :: PendingConnection -> IO (UUID, Connection)
initializeConnection pending = do
    connection <- acceptRequest pending
    -- FIXME: This is deprecated
    forkPingThread connection 30
    uuid <- nextRandom
    pure (uuid, connection)

-- | Run an IO function that keeps being applied to new messages being received
--   This function terminates when the connection is closed
runWithConnection :: (WebSocketsData a) => Connection -> (a -> IO ()) -> IO ()
runWithConnection connection f = handle disconnect . forever $ do
            msg <- receiveData connection
            f msg
            pure Nothing
    where
        disconnect :: SomeException -> IO ()
        disconnect _ = pure ()
