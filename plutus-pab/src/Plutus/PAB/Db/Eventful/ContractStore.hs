{-# LANGUAGE TypeOperators #-}
module Plutus.PAB.Db.Eventful.ContractStore(
    handleContractStore
    ) where

import           Control.Monad.Freer         (Eff, type (~>))
import           Plutus.PAB.Effects.Contract (ContractStore (..))

-- | Handle the 'ContractStore' effect by storing states
--   in the eventful database.
handleContractStore ::
    forall t effs.
    ContractStore t
    ~> Eff effs
handleContractStore = undefined -- FIXME: Implement
