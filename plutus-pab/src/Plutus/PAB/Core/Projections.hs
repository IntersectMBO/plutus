{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}
module Plutus.PAB.Core.Projections(
    installedContracts
    , installedContractsProjection
    ) where

import           Control.Monad.Freer
import           Data.Set                    (Set)
import           Eventful                    (Projection, StreamEvent (..), projectionMapMaybe)

import           Plutus.PAB.Effects.EventLog (EventLogEffect, runGlobalQuery)
import           Plutus.PAB.Events           (ChainEvent (..), UserEvent (..))
import           Plutus.PAB.Query            (setProjection)

installedContracts ::
    forall t effs.
    ( Ord t
    , Member (EventLogEffect (ChainEvent t)) effs
    )
    => Eff effs (Set t)
installedContracts = runGlobalQuery installedContractsProjection

installedContractsProjection ::
    forall t key position.
    Ord t => Projection (Set t) (StreamEvent key position (ChainEvent t))
installedContractsProjection = projectionMapMaybe contractPaths setProjection
  where
    contractPaths (StreamEvent _ _ (UserEvent (InstallContract contract))) =
        Just contract
    contractPaths _ = Nothing
