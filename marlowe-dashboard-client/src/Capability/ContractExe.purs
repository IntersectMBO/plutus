module Capability.ContractExe
  ( marloweContractExe
  , walletCompanionContractExe
  ) where

import Plutus.PAB.Effects.Contract.ContractExe (ContractExe(..))

foreign import marloweContractPath_ :: String

foreign import walletCompanionContractPath_ :: String

marloweContractExe :: ContractExe
marloweContractExe = ContractExe { contractPath: marloweContractPath_ }

walletCompanionContractExe :: ContractExe
walletCompanionContractExe = ContractExe { contractPath: walletCompanionContractPath_ }
