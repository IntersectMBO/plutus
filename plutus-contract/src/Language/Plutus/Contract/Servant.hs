{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
module Language.Plutus.Contract.Servant(
      contractServer
    , contractApp
    , initialResponse
    , runUpdate
    , Request(..)
    , Response(..)
    ) where

import           Control.Monad.Except                  (MonadError (..), runExcept)
import           Control.Monad.Writer
import qualified Data.Aeson                            as Aeson
import           Data.Bifunctor
import           Data.Proxy                            (Proxy (..))
import           Data.String                           (IsString (fromString))
import           GHC.Generics                          (Generic)
import           Servant                               ((:<|>) ((:<|>)), (:>), Get, JSON, Post, ReqBody, err500,
                                                        errBody)
import           Servant.Server                        (Application, ServantErr, Server, serve)

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Effects      (ContractEffects)
import           Language.Plutus.Contract.Prompt.Event (Event)
import           Language.Plutus.Contract.Prompt.Hooks (Hooks)
import           Language.Plutus.Contract.Record
import           Language.Plutus.Contract.Resumable    (ResumableError)
import qualified Language.Plutus.Contract.Resumable    as Resumable

newtype State = State { record :: Record Event }
    deriving stock (Eq, Show, Generic)
    deriving newtype (Aeson.FromJSON, Aeson.ToJSON)

data Request = Request
    { oldState :: State
    , event    :: Event
    }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (Aeson.FromJSON, Aeson.ToJSON)

data Response = Response
    { newState :: State
    , hooks    :: Hooks
    }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (Aeson.FromJSON, Aeson.ToJSON)

type ContractAPI =
       "initialise" :> Get '[JSON] Response
  :<|> "run" :> ReqBody '[JSON] Request :> Post '[JSON] Response

-- | Serve a 'PlutusContract' via the contract API.
contractServer :: Contract (ContractEffects '[]) () -> Server ContractAPI
contractServer con = initialise :<|> run where
    initialise = servantResp (initialResponse con)
    run req = servantResp (runUpdate con req)

servantResp :: MonadError ServantErr m => Either ResumableError Response -> m Response
servantResp = \case
        Left err ->
            let bd = "'insertAndUpdate' failed. " in
            throwError $ err500 { errBody = fromString (bd <> show err) }
        Right r -> pure r

-- | A servant 'Application' that serves a Plutus contract
contractApp :: Contract (ContractEffects '[]) () -> Application
contractApp = serve (Proxy @ContractAPI) . contractServer

runUpdate :: Contract (ContractEffects '[]) () -> Request -> Either ResumableError Response
runUpdate con (Request o e) =
    (\(r, h) -> Response (State r) h)
    <$> Resumable.insertAndUpdate (convertContract con) (record o) e

initialResponse :: Contract (ContractEffects '[]) () -> Either ResumableError Response
initialResponse =
    second (uncurry Response . first (State . fmap fst))
    . runExcept
    . runWriterT
    . Resumable.initialise
    . convertContract
