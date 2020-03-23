{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeOperators    #-}

module Plutus.SCB.EventLog where

import           Control.Monad         (void)
import           Control.Monad.Freer

import           Eventful              (Aggregate (..), GlobalStreamProjection)

import           Plutus.SCB.Core       (MonadEventStore (..), Source (..))
import           Plutus.SCB.Events     (ChainEvent (..))
import           Plutus.SCB.Query      (nullProjection)
import           Wallet.Emulator.Chain (ChainState (..))

-- | Event effects
data EventLogEffect r where
    -- Do we actually need this?
    UpdateProjection :: GlobalStreamProjection ChainState ChainEvent
                     -> EventLogEffect ()
    AppendEvent      :: ChainEvent -> EventLogEffect ()

updateProjection ::
    Member EventLogEffect effs
 => GlobalStreamProjection ChainState ChainEvent
 -> Eff effs ()
updateProjection oldProjection = send (UpdateProjection oldProjection)

appendEvent ::
    Member EventLogEffect effs
 => ChainEvent
 -> Eff effs ()
appendEvent event = send (AppendEvent event)

appendEvents ::
    Member EventLogEffect effs
 => [ChainEvent]
 -> Eff effs ()
appendEvents = mapM_ appendEvent

handleEventLog ::
    ( LastMember m effs
    , MonadEventStore ChainEvent m
    )
 => Eff (EventLogEffect ': effs) ~> Eff effs
handleEventLog = interpret $ \case
    UpdateProjection prj ->
        sendM $ void $ refreshProjection prj
    AppendEvent evt ->
        sendM $ do
          _ <- runCommand idAggregate NodeEventSource evt
          return ()
    where
      idAggregate :: Aggregate () ChainEvent ChainEvent
      idAggregate =
          Aggregate { aggregateProjection = nullProjection
                    , aggregateCommandHandler =
                        \() evt -> [evt]
                    }
