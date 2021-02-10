{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeOperators    #-}

module Control.Monad.Freer.Delay where

import           Control.Concurrent     (threadDelay)
import           Control.Monad.Freer    (Eff, LastMember, interpret, type (~>))
import           Control.Monad.Freer.TH (makeEffect)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Time.Units        (TimeUnit, toMicroseconds)

data DelayEffect r where
    DelayThread :: TimeUnit a => a -> DelayEffect ()

makeEffect ''DelayEffect

handleDelayEffect ::
       forall effs m. (LastMember m effs, MonadIO m)
    => Eff (DelayEffect ': effs) ~> Eff effs
handleDelayEffect =
    interpret $ \case
        DelayThread t ->
            liftIO . threadDelay . fromIntegral . toMicroseconds $ t
