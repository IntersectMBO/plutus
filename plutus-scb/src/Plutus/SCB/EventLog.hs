{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeOperators    #-}

module Plutus.SCB.EventLog where

import           Control.Lens                  hiding (index, modifying, use)
import           Control.Monad                 (void)
import           Control.Monad.Freer           (Eff, LastMember, Member, Members, type (~>), interpret, send, sendM)
import           Control.Monad.Freer.Extra.Log

import           Control.Monad.Freer.State     as Eff
import           Control.Monad.Freer.Writer
import           Eventful

import           Plutus.SCB.Core               (MonadEventStore (..), Source (..))
import           Plutus.SCB.Events
import           Plutus.SCB.Query              (nullProjection)
import           Wallet.Emulator.Chain         (ChainEffect (..), ChainState (..), handleChain, processBlock, queueTx)
import qualified Wallet.Emulator.Chain         as EM
import           Wallet.Emulator.NodeClient    (BlockValidated (..), NodeClientEffect (..), NodeClientEvent (..),
                                                NodeClientState (..), handleNodeClient)
-- | Event effects
data EventLogEffect r where
    UpdateProjection :: GlobalStreamProjection EM.ChainState ChainEvent
                     -> EventLogEffect ()
    AppendEvent      :: ChainEvent -> EventLogEffect ()

updateProjection ::
    Member EventLogEffect effs
 => GlobalStreamProjection EM.ChainState ChainEvent
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

-- | The `Chain` effect should be interpreted in terms
-- of the `LogEvent` effect
type LoggedChainEffs = '[State EM.ChainState, Writer [EM.ChainEvent], EventLogEffect]

handleLoggedChain :: (Members LoggedChainEffs effs)
                  => Eff (ChainEffect ': effs) ~> Eff effs
handleLoggedChain = interpret $ \case
    ProcessBlock -> do -- Note: This is something that only the mock server can use.
        block <- handleChain processBlock
        appendEvent (NodeEvent $ BlockAdded block)
        pure block

    QueueTx tx -> do
        handleChain (queueTx tx)
        appendEvent (NodeEvent $ SubmittedTx tx)

-- | The `NodeClient` effect should be interpreted in terms
-- of the `LogEvent` effect
type LoggedNodeClientEffs = '[ChainEffect, State ChainState, State NodeClientState, Writer [NodeClientEvent], Writer [EM.ChainEvent], EventLogEffect, State ClientStreamProjection, Log]

type ClientStreamProjection = GlobalStreamProjection ChainState ChainEvent

chainState :: Lens' ClientStreamProjection ChainState
chainState = lens getter setter where
    getter = streamProjectionState
    setter prj cs = prj { streamProjectionState = cs }

handleLoggedNodeClient ::(Members LoggedNodeClientEffs effs)
                       => Eff (NodeClientEffect ': effs) ~> Eff effs
handleLoggedNodeClient = interpret $ \case
    GetClientIndex -> error "Handled by the ChainIndex effect."
    ClientNotify (BlockValidated blk) -> do
        appendEvent (NodeEvent $ BlockAdded blk)
        get >>= updateProjection
    prg -> handleNodeClient (send prg)
