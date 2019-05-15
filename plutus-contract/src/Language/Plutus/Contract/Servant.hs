{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
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

import           Control.Monad.Writer
import qualified Data.Aeson                            as Aeson
import           Data.Bifunctor
import           Data.Proxy                            (Proxy (..))
import           Data.String                           (IsString (fromString))
import           GHC.Generics                          (Generic)
import           Servant                               ((:<|>) ((:<|>)), (:>), Get, JSON, Post, ReqBody, err500,
                                                        errBody, throwError)
import           Servant.Server                        (Application, Server, serve)

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Effects      (PlutusEffects)
import           Language.Plutus.Contract.Prompt.Event (Event)
import           Language.Plutus.Contract.Prompt.Hooks (Hooks)
import           Language.Plutus.Contract.Record
import qualified Language.Plutus.Contract.Resumable    as State

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
    -- , response :: -- user response / status
    }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (Aeson.FromJSON, Aeson.ToJSON)

type ContractAPI =
       "initialise" :> Get '[JSON] Response
  :<|> "run" :> ReqBody '[JSON] Request :> Post '[JSON] Response

-- | Serve a 'PlutusContract' via the contract API
contractServer :: Contract PlutusEffects () -> Server ContractAPI
contractServer con = initialise :<|> run where
    initialise = pure (initialResponse con)
    run req =
        case runUpdate con req of
            Left err ->
                let bd = "'insertAndUpdate' failed. " in
                throwError $ err500 { errBody = fromString (bd <> err) }
            Right r -> pure r

-- | A servant 'Application' that serves a Plutus contract
contractApp :: Contract PlutusEffects () -> Application
contractApp = serve (Proxy @ContractAPI) . contractServer

runUpdate :: Contract PlutusEffects () -> Request -> Either String Response
runUpdate con (Request o e) =
    (\(r, h) -> Response (State r) h)
    <$> State.insertAndUpdate (convertContract con) (record o) e

initialResponse :: Contract PlutusEffects () -> Response
initialResponse =
    uncurry Response
    . first (State . fmap fst)
    . runWriter
    . State.initialise
    . convertContract
