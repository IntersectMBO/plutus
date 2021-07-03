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
import           Data.UUID              (UUID)
import           Data.UUID.V4           (nextRandom)

data UUIDEffect r where
    UuidNextRandom :: UUIDEffect UUID
makeEffect ''UUIDEffect

handleUUIDEffect ::
    ( LastMember m effs
    , MonadIO m)
    => Eff (UUIDEffect ': effs)
    ~> Eff effs
handleUUIDEffect = interpret $ \case
    UuidNextRandom ->
      sendM $ liftIO nextRandom
