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
module Plutus.Contract.Servant(
      contractServer
    , contractApp
    , ContractRequest
    , ContractResponse
    ) where

import           Control.Monad.Except   (MonadError (..))
import           Data.Aeson             (FromJSON, ToJSON)
import           Data.Proxy             (Proxy (..))
import           Data.Row
import           Data.String            (IsString (fromString))
import           Servant                (Get, JSON, Post, ReqBody, (:<|>) ((:<|>)), (:>))
import           Servant.Server         (Application, Server, ServerError, err500, errBody, serve)

import           Plutus.Contract.Schema (Event, Handlers, Input, Output)
import           Plutus.Contract.State  (ContractRequest, ContractResponse, err)
import qualified Plutus.Contract.State  as ContractState
import           Plutus.Contract.Types  (Contract)

type ContractAPI w e s =
       "initialise" :> Get '[JSON] (ContractResponse w e (Event s) (Handlers s))
  :<|> "run" :> ReqBody '[JSON] (ContractRequest w (Event s)) :> Post '[JSON] (ContractResponse w e (Event s) (Handlers s))

-- | Serve a 'PlutusContract' via the contract API.
contractServer
    :: forall w s e.
    (Show e, Monoid w, ToJSON w, FromJSON w)
    => Contract w s e ()
    -> Server (ContractAPI w e s)
contractServer con = initialise :<|> run where
    initialise = servantResp $ ContractState.initialiseContract con
    run req = servantResp $ ContractState.insertAndUpdateContract con req

servantResp
    :: (Show e, MonadError ServerError m)
    => (ContractResponse w e (Event s) (Handlers s))
    -> m (ContractResponse w e (Event s) (Handlers s))
servantResp r = case err r of
        Just e ->
            let bd = "'insertAndUpdate' failed. " in
            throwError $ err500 { errBody = fromString (bd <> show e) }
        Nothing -> pure r

-- | A servant 'Application' that serves a Plutus contract
contractApp
    :: forall w s e.
       ( AllUniqueLabels (Input s)
       , Forall (Input s) FromJSON
       , Forall (Input s) ToJSON
       , Forall (Output s) ToJSON
       , ToJSON e
       , ToJSON w
       , FromJSON w
       , Monoid w
       , Show e
       )
    => Contract w s e () -> Application
contractApp = serve (Proxy @(ContractAPI w e s)) . contractServer @w @s
