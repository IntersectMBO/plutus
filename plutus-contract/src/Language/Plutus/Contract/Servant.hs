{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.Plutus.Contract.Servant(
      contractServer
    , contractApp
    , ContractRequest
    , ContractResponse
    ) where

import           Control.Monad.Except            (MonadError (..))
import           Data.Aeson                      (FromJSON, ToJSON)
import           Data.Proxy                      (Proxy (..))
import           Data.Row
import           Data.String                     (IsString (fromString))
import           Servant                         (Get, JSON, Post, ReqBody, (:<|>) ((:<|>)), (:>))
import           Servant.Server                  (Application, Server, ServerError, err500, errBody, serve)

import           Language.Plutus.Contract.Schema (Event, Handlers, Input, Output)
import           Language.Plutus.Contract.State  (ContractRequest, ContractResponse, err)
import qualified Language.Plutus.Contract.State  as ContractState
import           Language.Plutus.Contract.Types  (Contract)

type ContractAPI e s =
       "initialise" :> Get '[JSON] (ContractResponse e (Event s) (Handlers s))
  :<|> "run" :> ReqBody '[JSON] (ContractRequest (Event s)) :> Post '[JSON] (ContractResponse e (Event s) (Handlers s))

-- | Serve a 'PlutusContract' via the contract API.
contractServer
    :: forall s e.
    ( Show e )
    => Contract s e ()
    -> Server (ContractAPI e s)
contractServer con = initialise :<|> run where
    initialise = servantResp $ ContractState.initialiseContract con
    run req = servantResp $ ContractState.insertAndUpdateContract con req

servantResp
    :: (Show e, MonadError ServerError m)
    => (ContractResponse e (Event s) (Handlers s))
    -> m (ContractResponse e (Event s) (Handlers s))
servantResp r = case err r of
        Just e ->
            let bd = "'insertAndUpdate' failed. " in
            throwError $ err500 { errBody = fromString (bd <> show e) }
        Nothing -> pure r

-- | A servant 'Application' that serves a Plutus contract
contractApp
    :: forall s e.
       ( AllUniqueLabels (Input s)
       , Forall (Input s) FromJSON
       , Forall (Input s) ToJSON
       , Forall (Output s) ToJSON
       , ToJSON e
       , Show e
       )
    => Contract s e () -> Application
contractApp = serve (Proxy @(ContractAPI e s)) . contractServer @s
