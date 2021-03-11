{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
module Plutus.PAB.Db.Eventful.ContractDefinitionStore(
    handleContractDefinitionStore
    ) where


import           Control.Monad                (void)
import           Control.Monad.Freer          (Eff, Member, type (~>))
import qualified Data.Set                     as Set
import qualified Plutus.PAB.Command           as Command
import qualified Plutus.PAB.Db.Eventful.Query as Query
import           Plutus.PAB.Effects.Contract  (ContractDefinitionStore (..), PABContract (..))
import           Plutus.PAB.Effects.EventLog  (EventLogEffect, runCommand, runGlobalQuery)
import           Plutus.PAB.Events            (PABEvent)
import           Plutus.PAB.Types             (Source (..))

-- | Handle the 'ContractDefinitionStore' effect by storing definitions
--   in the eventful database.
handleContractDefinitionStore ::
    forall t effs.
    ( Member (EventLogEffect (PABEvent (ContractDef t))) effs
    , Ord (ContractDef t)
    )
    => ContractDefinitionStore t
    ~> Eff effs
handleContractDefinitionStore = \case
    AddDefinition t ->
        void
            $ runCommand @() @(PABEvent (ContractDef t))
                Command.installCommand
                PABEventSource
                t
    GetDefinitions ->
        Set.toList <$> runGlobalQuery (Query.installedContractsProjection @(ContractDef t))
