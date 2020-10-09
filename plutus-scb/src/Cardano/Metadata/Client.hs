{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Cardano.Metadata.Client
    ( handleMetadataClient
    ) where
import           Cardano.Metadata.API      (API)
import           Cardano.Metadata.Types    (JSONEncoding (ExternalEncoding),
                                            MetadataEffect (GetProperties, GetProperty),
                                            MetadataError (MetadataClientError))
import           Control.Monad.Freer       (Eff, LastMember, Member, type (~>), interpret, sendM)
import           Control.Monad.Freer.Error (Error, throwError)
import           Control.Monad.IO.Class    (MonadIO, liftIO)
import           Data.Coerce               (coerce)
import           Data.Proxy                (Proxy (Proxy))
import           Network.HTTP.Types        (status404)
import           Servant.Client            (ClientEnv, ClientError (FailureResponse), ClientM, client,
                                            responseStatusCode, runClientM)
import           Servant.Extra             (left, right)

handleMetadataClient ::
       forall m effs.
       (LastMember m effs, MonadIO m, Member (Error MetadataError) effs)
    => ClientEnv
    -> Eff (MetadataEffect ': effs) ~> Eff effs
handleMetadataClient clientEnv =
        -- The api can be flipped between 'AesonEncoding' and
        -- 'ExternalEncoding' depending on which metadata server
        -- we're using. See the notes on this, and 'coerce', in
        -- 'Cardano.Metadata.Types'.
    let api = client (Proxy @(API 'ExternalEncoding))

        (getProperties, getProperty) = (left . api, right . api)

        runClient :: ClientM (Maybe a) -> Eff effs (Maybe a)
        runClient action = do
            result <- sendM $ liftIO $ runClientM action clientEnv
            case result of
                Right value -> pure value
                (Left (FailureResponse _ response))
                    | responseStatusCode response == status404 -> pure Nothing
                (Left err) -> throwError $ MetadataClientError err
     in interpret $ \case
            GetProperties subject ->
                coerce <$> runClient (getProperties subject)
            GetProperty subject propertyKey ->
                coerce <$> runClient (getProperty subject propertyKey)
