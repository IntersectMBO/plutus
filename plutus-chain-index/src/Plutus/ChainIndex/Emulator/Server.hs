{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
module Plutus.ChainIndex.Emulator.Server(
    serveChainIndexQueryServer,
    serveChainIndex) where

import           Control.Concurrent.STM              (TVar)
import qualified Control.Concurrent.STM              as STM
import qualified Control.Monad.Except                as E
import           Control.Monad.Freer                 (Eff, interpret, run, type (~>))
import           Control.Monad.Freer.Error           (Error, runError)
import           Control.Monad.Freer.Extras.Log      (handleLogIgnore)
import           Control.Monad.Freer.Extras.Modify   (raiseEnd)
import           Control.Monad.Freer.State           (evalState)
import           Control.Monad.IO.Class              (MonadIO (liftIO))
import qualified Data.ByteString.Lazy                as BSL
import           Data.Proxy                          (Proxy (..))
import qualified Data.Text                           as Text
import qualified Data.Text.Encoding                  as Text
import qualified Network.Wai.Handler.Warp            as Warp
import           Plutus.ChainIndex                   (ChainIndexError, ChainIndexLog)
import           Plutus.ChainIndex.Api               (API)
import           Plutus.ChainIndex.Effects           (ChainIndexControlEffect, ChainIndexQueryEffect)
import           Plutus.ChainIndex.Emulator.Handlers (ChainIndexEmulatorState (..), handleControl, handleQuery)
import           Plutus.ChainIndex.Server            hiding (serveChainIndexQueryServer)
import           Servant.Server                      (Handler, ServerError, err500, errBody, hoistServer, serve)

serveChainIndexQueryServer ::
    Int -- ^ Port
    -> TVar ChainIndexEmulatorState -- ^ Chain index state (TODO: When the disk state is stored in a DB, replace this with DB connection info)
    -> IO ()
serveChainIndexQueryServer port diskState = do
    let server = hoistServer (Proxy @API) (runChainIndexQuery diskState) serveChainIndex
    Warp.run port (serve (Proxy @API) server)

runChainIndexQuery ::
    TVar ChainIndexEmulatorState
    -> Eff '[ChainIndexQueryEffect, ChainIndexControlEffect, Error ServerError] ~> Handler
runChainIndexQuery emState_ action = do
    emState <- liftIO (STM.readTVarIO emState_)
    let result = run
                    $ evalState emState
                    $ runError @ChainIndexError
                    $ handleLogIgnore @ChainIndexLog
                    $ runError
                    $ interpret handleControl
                    $ interpret handleQuery
                    $ raiseEnd action
    case result of
        Right (Right a) -> pure a
        Right (Left e) -> E.throwError e
        Left e' ->
            let err = err500 { errBody = BSL.fromStrict $ Text.encodeUtf8 $ Text.pack $ show e' } in
            E.throwError err
