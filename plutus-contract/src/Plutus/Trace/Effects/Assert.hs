{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-

An effect for assertion that the specified condition holds.

-}
module Plutus.Trace.Effects.Assert(
    Assert(..)
    , assert
    , handleAssert
    ) where

import           Control.Monad                 (unless)
import           Control.Monad.Freer           (Eff, Member, type (~>))
import           Control.Monad.Freer.Coroutine (Yield)
import           Control.Monad.Freer.Error     (Error, throwError)
import           Control.Monad.Freer.State     (State, get)
import           Control.Monad.Freer.TH        (makeEffect)
import           Plutus.Trace.Emulator.Types   (EmulatorMessage, EmulatorRuntimeError (AssertionError))
import           Plutus.Trace.Scheduler        (EmSystemCall)
import           Wallet.Emulator.MultiAgent    (EmulatorState)

data Assert r where
    Assert :: String -> (EmulatorState -> Bool) -> Assert ()

makeEffect ''Assert

-- | Pass 'EmulatorState' to the provided predicate and throw error unless it's true.
handleAssert ::
    forall effs effs2.
    ( Member (Yield (EmSystemCall effs2 EmulatorMessage) (Maybe EmulatorMessage)) effs
    , Member (Error EmulatorRuntimeError) effs
    , Member (State EmulatorState) effs
    )
    => Assert
    ~> Eff effs
handleAssert = \case
    Assert name predicate -> do
        emulatorState <- get @EmulatorState
        unless (predicate emulatorState) $ throwError (AssertionError name)
