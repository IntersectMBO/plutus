{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeOperators    #-}

module Plutus.SCB.EventLog where

import           Control.Lens              hiding (index)
import           Control.Monad.Freer

import           Eventful                  (Aggregate (..), GlobalStreamProjection)

import           Plutus.SCB.Core           (MonadEventStore (..), Source (..))
import           Plutus.SCB.Events         (ChainEvent (..))
import           Plutus.SCB.Query          (nullProjection)

-- | Event effects
data EventLogState pjs =
     EventLogState { _elsEvents      :: [ChainEvent]
                   , _elsProjections :: pjs }
makeLenses ''EventLogState

data EventLogEffect r where
    UpdateProjection :: GlobalStreamProjection state ChainEvent
                     -> EventLogEffect (GlobalStreamProjection state ChainEvent)
    AppendEvent      :: ChainEvent -> EventLogEffect ()

updateProjection :: Member EventLogEffect effs
                 => GlobalStreamProjection state ChainEvent
                 -> Eff effs (GlobalStreamProjection state ChainEvent)
updateProjection oldProjection = send (UpdateProjection oldProjection)

appendEvent :: Member EventLogEffect effs
            => ChainEvent
            -> Eff effs ()
appendEvent event = send (AppendEvent event)

handleEventLog ::
    ( LastMember m effs
    , MonadEventStore ChainEvent m
    )
 => Eff (EventLogEffect ': effs) ~> Eff effs
handleEventLog = interpret $ \case
    UpdateProjection prj ->
        sendM $ refreshProjection prj
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
