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
import           Plutus.PAB.Events           (PABEvent (..))
import           Plutus.PAB.Query            (setProjection)

-- FIXME: move to Plutus.PAB.Db.Eventful.Projections
installedContracts ::
    forall t effs.
    ( Ord t
    , Member (EventLogEffect (PABEvent t)) effs
    )
    => Eff effs (Set t)
installedContracts = runGlobalQuery installedContractsProjection

installedContractsProjection ::
    forall t key position.
    Ord t => Projection (Set t) (StreamEvent key position (PABEvent t))
installedContractsProjection = projectionMapMaybe contractPaths setProjection
  where
    contractPaths (StreamEvent _ _ (InstallContract contract)) =
        Just contract
    contractPaths _ = Nothing
