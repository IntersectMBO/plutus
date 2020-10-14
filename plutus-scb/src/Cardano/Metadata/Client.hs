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
import           Cardano.Metadata.Types    (JSONEncoding (AesonEncoding),
                                            MetadataEffect (BatchQuery, GetProperties, GetProperty),
                                            MetadataError (MetadataClientError, SubjectNotFound, SubjectPropertyNotFound))
import           Control.Monad.Freer       (Eff, LastMember, Member, type (~>), interpret, sendM)
import           Control.Monad.Freer.Error (Error, throwError)
import           Control.Monad.IO.Class    (MonadIO, liftIO)
import           Data.Coerce               (Coercible, coerce)
import           Data.Proxy                (Proxy (Proxy))
import           Network.HTTP.Types        (status404)
import           Servant.Client            (Client, ClientEnv, ClientError (FailureResponse), ClientM, client,
                                            responseStatusCode, runClientM)
import           Servant.Extra             (left, right)

-- Maintainer's Note: The api can be flipped between 'AesonEncoding'
-- and 'ExternalEncoding' depending on which metadata server we're
-- using. See the notes on this, and 'coerce', in
-- 'Cardano.Metadata.Types'.
api :: Client ClientM (API 'AesonEncoding)
api = client (Proxy @(API _))

handleMetadataClient ::
       forall m effs.
       (LastMember m effs, MonadIO m, Member (Error MetadataError) effs)
    => ClientEnv
    -> Eff (MetadataEffect ': effs) ~> Eff effs
handleMetadataClient clientEnv =
    let getProperties subject = left (left api subject)
        getProperty subject = right (left api subject)
        batchQuery = right api
        runIt :: Coercible a b => ClientM b -> Eff effs (Either ClientError a)
        runIt = fmap coerce . sendM . liftIO . flip runClientM clientEnv
        runClient :: Coercible a b => Eff effs a -> ClientM b -> Eff effs a
        runClient def action = do
            result <- runIt action
            case result of
                (Right value) -> pure value
                (Left (FailureResponse _ response))
                    | responseStatusCode response == status404 -> def
                (Left err) -> throwError $ MetadataClientError err
     in interpret $ \case
            GetProperties subject ->
                runClient
                    (throwError (SubjectNotFound subject))
                    (getProperties subject)
            GetProperty subject propertyKey ->
                runClient
                    (throwError (SubjectPropertyNotFound subject propertyKey))
                    (getProperty subject propertyKey)
            BatchQuery query -> runClient (pure []) (batchQuery query)
