{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
module Plutus.ChainIndex.Server(
    serveChainIndexQueryServer,
    serveChainIndex) where

import           Control.Monad                     ((>=>))
import qualified Control.Monad.Except              as E
import           Control.Monad.Freer               (Eff, Member, type (~>))
import           Control.Monad.Freer.Error         (Error, runError, throwError)
import           Control.Monad.Freer.Extras.Modify (raiseEnd)
import           Control.Monad.IO.Class            (MonadIO (liftIO))
import qualified Data.ByteString.Lazy              as BSL
import           Data.Default                      (Default (def))
import           Data.Maybe                        (fromMaybe)
import           Data.Proxy                        (Proxy (..))
import qualified Data.Text                         as Text
import qualified Data.Text.Encoding                as Text
import qualified Network.Wai.Handler.Warp          as Warp
import           Plutus.ChainIndex                 (RunRequirements, runChainIndexEffects)
import           Plutus.ChainIndex.Api             (API, FromHashAPI, UtxoAtAddressRequest (UtxoAtAddressRequest),
                                                    UtxoWithCurrencyRequest (UtxoWithCurrencyRequest))
import           Plutus.ChainIndex.Effects         (ChainIndexControlEffect, ChainIndexQueryEffect)
import qualified Plutus.ChainIndex.Effects         as E
import           Servant.API                       ((:<|>) (..))
import           Servant.API.ContentTypes          (NoContent (..))
import           Servant.Server                    (Handler, ServerError, ServerT, err404, err500, errBody, hoistServer,
                                                    serve)

serveChainIndexQueryServer ::
    Int -- ^ Port
    -> RunRequirements
    -> IO ()
serveChainIndexQueryServer port runReq = do
    let server = hoistServer (Proxy @API) (runChainIndexQuery runReq) serveChainIndex
    Warp.run port (serve (Proxy @API) server)

runChainIndexQuery ::
    RunRequirements
    -> Eff '[Error ServerError, ChainIndexQueryEffect, ChainIndexControlEffect] ~> Handler
runChainIndexQuery runReq action = do
    (result, _) <- liftIO $ runChainIndexEffects runReq $ runError $ raiseEnd action
    case result of
        Right (Right a) -> pure a
        Right (Left e) -> E.throwError e
        Left e' ->
            let err = err500 { errBody = BSL.fromStrict $ Text.encodeUtf8 $ Text.pack $ show e' } in
            E.throwError err

serveChainIndex ::
    forall effs.
    ( Member (Error ServerError) effs
    , Member ChainIndexQueryEffect effs
    , Member ChainIndexControlEffect effs
    )
    => ServerT API (Eff effs)
serveChainIndex =
    pure NoContent
    :<|> serveFromHashApi
    :<|> (E.txOutFromRef >=> handleMaybe)
    :<|> (E.txFromTxId >=> handleMaybe)
    :<|> E.utxoSetMembership
    :<|> (\(UtxoAtAddressRequest pq c) -> E.utxoSetAtAddress (fromMaybe def pq) c)
    :<|> (\(UtxoWithCurrencyRequest pq c) -> E.utxoSetWithCurrency (fromMaybe def pq) c)
    :<|> E.getTip
    :<|> E.collectGarbage *> pure NoContent
    :<|> E.getDiagnostics

serveFromHashApi ::
    forall effs.
    ( Member (Error ServerError) effs
    , Member ChainIndexQueryEffect effs
    )
    => ServerT FromHashAPI (Eff effs)
serveFromHashApi =
    (E.datumFromHash >=> handleMaybe)
    :<|> (E.validatorFromHash >=> handleMaybe)
    :<|> (E.mintingPolicyFromHash >=> handleMaybe)
    :<|> (E.stakeValidatorFromHash >=> handleMaybe)
    :<|> (E.redeemerFromHash >=> handleMaybe)

-- | Return the value of throw a 404 error
handleMaybe :: forall effs. Member (Error ServerError) effs => Maybe ~> Eff effs
handleMaybe = maybe (throwError err404) pure
