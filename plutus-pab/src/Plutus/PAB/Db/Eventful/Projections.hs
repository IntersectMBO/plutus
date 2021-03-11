{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}
{-

@eventful@ projections for the PAB

-}
module Plutus.PAB.Db.Eventful.Projections(
    installedContracts
    , installedContractsProjection
    ) where

import           Control.Monad.Freer
import           Data.Set                     (Set)
import           Eventful                     (Projection, StreamEvent (..), projectionMapMaybe)

import           Plutus.PAB.Db.Eventful.Query (setProjection)
import           Plutus.PAB.Effects.EventLog  (EventLogEffect, runGlobalQuery)
import           Plutus.PAB.Events            (PABEvent (..))

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
