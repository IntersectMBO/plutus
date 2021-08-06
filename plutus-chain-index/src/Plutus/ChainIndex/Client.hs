{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
module Plutus.ChainIndex.Client(
    -- * HTTP Client handler
    handleChainIndexClient
    -- * Servant client functions
    , healthCheck
    , getDatum
    , getValidator
    , getMintingPolicy
    , getStakeValidator
    , getTxOut
    , getTx
    , getIsUtxo
    , getUtxoAtAddress
    , getTip
    ) where

import           Control.Monad.Freer          (Eff, LastMember, Member, sendM, type (~>))
import           Control.Monad.Freer.Error    (Error, throwError)
import           Control.Monad.Freer.Reader   (Reader, ask)
import           Control.Monad.IO.Class       (MonadIO (..))
import           Data.Proxy                   (Proxy (..))
import           Ledger                       (Datum, DatumHash, MintingPolicy, MintingPolicyHash, StakeValidator,
                                               StakeValidatorHash, TxId, Validator, ValidatorHash)
import           Ledger.Credential            (Credential)
import           Ledger.Tx                    (ChainIndexTxOut, TxOutRef)
import           Network.HTTP.Types.Status    (Status (..))
import           Plutus.ChainIndex.Api        (API)
import           Plutus.ChainIndex.Effects    (ChainIndexQueryEffect (..))
import           Plutus.ChainIndex.Tx         (ChainIndexTx)
import           Plutus.ChainIndex.Types      (Page, Tip)
import           Servant                      (NoContent, (:<|>) (..))
import           Servant.Client               (ClientEnv, ClientError (..), ClientM, client, runClientM)
import           Servant.Client.Core.Response (ResponseF (..))

healthCheck :: ClientM NoContent

-- TODO: Catch 404 error
getDatum :: DatumHash -> ClientM Datum
getValidator :: ValidatorHash -> ClientM Validator
getMintingPolicy :: MintingPolicyHash -> ClientM MintingPolicy
getStakeValidator :: StakeValidatorHash -> ClientM StakeValidator

getTxOut :: TxOutRef -> ClientM ChainIndexTxOut
getTx :: TxId -> ClientM ChainIndexTx
getIsUtxo :: TxOutRef -> ClientM (Tip, Bool)
getUtxoAtAddress :: Credential -> ClientM (Tip, Page TxOutRef)
getTip :: ClientM Tip

(healthCheck, (getDatum, getValidator, getMintingPolicy, getStakeValidator), getTxOut, getTx, getIsUtxo, getUtxoAtAddress, getTip) =
    (healthCheck_, (getDatum_, getValidator_, getMintingPolicy_, getStakeValidator_), getTxOut_, getTx_, getIsUtxo_, getUtxoAtAddress_, getTip_) where
        healthCheck_
            :<|> (getDatum_ :<|> getValidator_ :<|> getMintingPolicy_ :<|> getStakeValidator_)
            :<|> getTxOut_
            :<|> getTx_
            :<|> getIsUtxo_
            :<|> getUtxoAtAddress_
            :<|> getTip_ = client (Proxy @API)

-- | Handle 'ChainIndexQueryEffect' by making HTTP calls to a remote
--   server.
handleChainIndexClient ::
    forall m effs.
    ( LastMember m effs
    , Member (Reader ClientEnv) effs
    , MonadIO m
    , Member (Error ClientError) effs
    )
    => ChainIndexQueryEffect
    ~> Eff effs
handleChainIndexClient event = do
    clientEnv <- ask
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure
        runClientMaybe :: forall a. ClientM a -> Eff effs (Maybe a)
        runClientMaybe a = do
            response <- sendM $ liftIO $ runClientM a clientEnv
            case response of
                Right a'                                                                     -> pure (Just a')

                -- convert 404 (NOT FOUND) to 'Nothing'
                Left (FailureResponse _ Response{responseStatusCode=Status{statusCode=404}}) -> pure Nothing
                Left e                                                                       -> throwError e
    case event of
        DatumFromHash d          -> runClientMaybe (getDatum d)
        ValidatorFromHash d      -> runClientMaybe (getValidator d)
        MintingPolicyFromHash d  -> runClientMaybe (getMintingPolicy d)
        StakeValidatorFromHash d -> runClientMaybe (getStakeValidator d)
        TxOutFromRef r           -> runClientMaybe (getTxOut r)
        TxFromTxId t             -> runClientMaybe (getTx t)
        UtxoSetMembership r      -> runClient (getIsUtxo r)
        UtxoSetAtAddress a       -> runClient (getUtxoAtAddress a)
        GetTip                   -> runClient getTip
