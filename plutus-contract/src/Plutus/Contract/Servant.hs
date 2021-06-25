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

import           Control.Monad.Except    (MonadError (..))
import           Data.Aeson              (FromJSON, ToJSON)
import           Data.Proxy              (Proxy (..))
import           Data.String             (IsString (fromString))
import           Plutus.Contract.Effects (PABReq, PABResp)
import           Servant                 (Get, JSON, Post, ReqBody, (:<|>) ((:<|>)), (:>))
import           Servant.Server          (Application, Server, ServerError, err500, errBody, serve)

import           Plutus.Contract.State   (ContractRequest, ContractResponse, err)
import qualified Plutus.Contract.State   as ContractState
import           Plutus.Contract.Types   (Contract)

type ContractAPI w e =
       "initialise" :> Get '[JSON] (ContractResponse w e PABResp PABReq)
  :<|> "run" :> ReqBody '[JSON] (ContractRequest w PABResp) :> Post '[JSON] (ContractResponse w e PABResp PABReq)

-- | Serve a 'PlutusContract' via the contract API.
contractServer
    :: forall w s e.
    (Show e, Monoid w)
    => Contract w s e ()
    -> Server (ContractAPI w e)
contractServer con = initialise :<|> run where
    initialise = servantResp $ ContractState.initialiseContract con
    run req = servantResp $ ContractState.insertAndUpdateContract con req

servantResp
    :: (Show e, MonadError ServerError m)
    => (ContractResponse w e PABResp PABReq)
    -> m (ContractResponse w e PABResp PABReq)
servantResp r = case err r of
        Just e ->
            let bd = "'insertAndUpdate' failed. " in
            throwError $ err500 { errBody = fromString (bd <> show e) }
        Nothing -> pure r

-- | A servant 'Application' that serves a Plutus contract
contractApp
    :: forall w s e.
       ( ToJSON e
       , ToJSON w
       , FromJSON w
       , Monoid w
       , Show e
       )
    => Contract w s e () -> Application
contractApp = serve (Proxy @(ContractAPI w e)) . contractServer @w @s
