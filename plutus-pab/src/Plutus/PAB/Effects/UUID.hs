{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeOperators    #-}
module Plutus.PAB.Effects.UUID where

import           Control.Monad.Freer
import           Control.Monad.Freer.TH (makeEffect)
import           Control.Monad.IO.Class (MonadIO (..))
import           Eventful.UUID          (UUID)
import qualified Eventful.UUID          as UUID

data UUIDEffect r where
    UuidNextRandom :: UUIDEffect UUID
makeEffect ''UUIDEffect

handleUUIDEffect ::
    ( LastMember m effs
    , MonadIO m)
    => Eff (UUIDEffect ': effs)
    ~> Eff effs
handleUUIDEffect = interpret $ \case
    UuidNextRandom -> sendM $ liftIO UUID.uuidNextRandom
