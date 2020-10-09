{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Cardano.Metadata.Client where

import           Cardano.Metadata.API      (API)
import           Cardano.Metadata.Types    (MetadataEffect (GetProperties, GetProperty), Property, PropertyKey, Subject)
import           Control.Monad.Freer       (Eff, LastMember, Member, type (~>), interpret, sendM)
import           Control.Monad.Freer.Error (Error, throwError)
import           Control.Monad.IO.Class    (MonadIO, liftIO)
import           Data.Proxy                (Proxy (Proxy))
import           Servant.Client            (ClientEnv, ClientError, ClientM, client, runClientM)
import           Servant.Extra             (left, right)

getProperties :: Subject -> ClientM [Property]
getProperty :: Subject -> PropertyKey -> ClientM Property
(getProperties, getProperty) = (_getProperties, _getProperty)
  where
    _getProperties = left . api
    _getProperty = right . api
    api = client (Proxy @API)

handleMetadataClient ::
       forall m effs.
       (LastMember m effs, MonadIO m, Member (Error ClientError) effs)
    => ClientEnv
    -> Eff (MetadataEffect ': effs) ~> Eff effs
handleMetadataClient clientEnv =
    let runClient :: forall a. ClientM a -> Eff effs a
        runClient a =
            (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure
     in interpret $ \case
            GetProperties subject -> runClient $ getProperties subject
            GetProperty subject propertyKey ->
                runClient $ getProperty subject propertyKey
