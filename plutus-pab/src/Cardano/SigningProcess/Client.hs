{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Cardano.SigningProcess.Client where

import           Cardano.SigningProcess.API (API)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error  (Error, throwError)
import           Control.Monad.IO.Class     (MonadIO (..))
import           Data.Proxy                 (Proxy (Proxy))
import           Ledger                     (PubKeyHash, Tx)
import           Servant.Client             (ClientEnv, ClientError, ClientM, client, runClientM)
import           Wallet.Effects             (SigningProcessEffect (..))

addSignatures :: [PubKeyHash] -> Tx -> ClientM Tx
addSignatures = curry addSignatures_ where
    addSignatures_ = client (Proxy @API)

handleSigningProcessClient ::
    forall m effs.
    ( LastMember m effs
    , MonadIO m
    , Member (Error ClientError) effs
    )
    => ClientEnv
    -> SigningProcessEffect
    ~> Eff effs
handleSigningProcessClient clientEnv =
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure
    in
      \case
        AddSignatures sigs tx -> runClient (addSignatures sigs tx)
