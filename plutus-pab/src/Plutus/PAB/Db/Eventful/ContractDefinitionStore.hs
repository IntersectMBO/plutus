{-# LANGUAGE TypeOperators #-}
module Plutus.PAB.Db.Eventful.ContractDefinitionStore(
    handleContractDefinitionStore
    ) where

import           Control.Monad.Freer         (Eff, type (~>))
import           Plutus.PAB.Effects.Contract (ContractDefinitionStore (..))

-- | Handle the 'ContractDefinitionStore' effect by storing definitions
--   in the eventful database.
handleContractDefinitionStore ::
    forall t effs.
    ContractDefinitionStore t
    ~> Eff effs
handleContractDefinitionStore = undefined
