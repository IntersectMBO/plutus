{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.Plutus.Contract.Servant(
      contractServer
    , contractApp
    , initialResponse
    , runUpdate
    , Request(..)
    , Response(..)
    ) where

import           Control.Monad.Except               (MonadError (..), runExcept)
import           Control.Monad.Writer               (runWriterT)
import           Data.Aeson                         (FromJSON, ToJSON)
import           Data.Bifunctor
import           Data.Proxy                         (Proxy (..))
import           Data.Row
import           Data.String                        (IsString (fromString))
import           GHC.Generics                       (Generic)
import           Servant                            ((:<|>) ((:<|>)), (:>), Get, JSON, Post, ReqBody, err500, errBody)
import           Servant.Server                     (Application, ServantErr, Server, serve)

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Record
import           Language.Plutus.Contract.Resumable (ResumableError)
import qualified Language.Plutus.Contract.Resumable as Resumable
import           Language.Plutus.Contract.Schema    (Event, Handlers, Input, Output)

newtype State e = State { record :: Record e }
    deriving stock (Generic, Eq)
    deriving newtype (ToJSON, FromJSON)

data Request s = Request
    { oldState :: State (Event s)
    , event    :: Event s
    }
    deriving stock (Generic)

instance (AllUniqueLabels (Input s), Forall (Input s) FromJSON) => FromJSON (Request s)
instance (Forall (Input s) ToJSON) => ToJSON (Request s)

data Response s = Response
    { newState :: State (Event s)
    , hooks    :: Handlers s
    }
    deriving stock (Generic)

instance (AllUniqueLabels (Input s), AllUniqueLabels (Output s), Forall (Input s) FromJSON, Forall (Output s) FromJSON) => FromJSON (Response s)
instance (Forall (Input s) ToJSON, Forall (Output s) ToJSON) => ToJSON (Response s)

type ContractAPI s =
       "initialise" :> Get '[JSON] (Response s)
  :<|> "run" :> ReqBody '[JSON] (Request s) :> Post '[JSON] (Response s)

-- | Serve a 'PlutusContract' via the contract API.
contractServer
    :: forall s.
       ( AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       )
    => Contract s ()
    -> Server (ContractAPI s)
contractServer con = initialise :<|> run where
    initialise = servantResp (initialResponse con)
    run req = servantResp (runUpdate con req)

servantResp :: MonadError ServantErr m => Either ResumableError (Response s) -> m (Response s)
servantResp = \case
        Left err ->
            let bd = "'insertAndUpdate' failed. " in
            throwError $ err500 { errBody = fromString (bd <> show err) }
        Right r -> pure r

-- | A servant 'Application' that serves a Plutus contract
contractApp
    :: forall s.
       ( AllUniqueLabels (Output s)
       , AllUniqueLabels (Input s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       , Forall (Input s) FromJSON
       , Forall (Input s) ToJSON
       , Forall (Output s) ToJSON )
    => Contract s () -> Application
contractApp = serve (Proxy @(ContractAPI s)) . contractServer @s

runUpdate
    :: forall s.
       (AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       )
    => Contract s () -> Request s -> Either ResumableError (Response s)
runUpdate con (Request o e) =
    (\(r, h) -> Response (State r) h)
    <$> Resumable.insertAndUpdate con (record o) e

initialResponse
    :: forall s.
       ( AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       )
    => Contract s ()
    -> Either ResumableError (Response s)
initialResponse =
    fmap (uncurry Response . first (State . fmap fst))
    . runExcept
    . runWriterT
    . Resumable.initialise
