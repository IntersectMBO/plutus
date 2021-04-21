module Capability.ContractExe
  ( ContractType(..)
  , contractExe
  , contractType
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe(..))

foreign import walletCompanionContractPath_ :: String

foreign import controlContractPath_ :: String

foreign import followContractPath_ :: String

-- Note [Marlowe Plutus contract types]: Marlowe Run needs three Plutus contracts to be
-- available in the PAB:
--   1. The WalletCompanionContract. Each wallet starts one of these when it is created. It
--      listens continuously for payments of role tokens to that wallet, and updates its
--      observable state with an array of `(MarloweParams, MarloweData)`, one pair for each
--      role token, hence one for each Marlowe contract for which this wallet has a role.
--      We use this to determine when we need to create new MarloweContract instances.
--   2. The ControlContract. We use this to "create" Marlowe contracts (i.e. to set them up
--      on the blockchain, distributing the role tokens), and to "apply-inputs" to a
--      Marlowe contract (i.e. perform an action in that contract).
--   3. The FollowContract. We use this to "follow" a Marlowe contract. Once a contract has
--      been "created", and we have its MarloweParams, we use an instance of the
--      FollowContract to track its history and status. Once we have called the "follow"
--      endpoint (passing it the MarloweParams), its observable state will tell us
--      everything we need to know about the contract, and will be updated when it changes.
-- Each wallet should always have one WalletCompanionContract running and one
-- ControlContract running (these are started when the wallet is generated), and then zero
-- or more FollowContracts (one for each Marlowe contract for which they have a role). The
-- latter are created each time the wallet receives a new role token (which we are told
-- about by the WalletCompanionContract).
data ContractType
  = WalletCompanionContract
  | ControlContract
  | FollowContract

contractExe :: ContractType -> ContractExe
contractExe WalletCompanionContract = ContractExe { contractPath: walletCompanionContractPath_ }

contractExe ControlContract = ContractExe { contractPath: controlContractPath_ }

contractExe FollowContract = ContractExe { contractPath: followContractPath_ }

contractType :: ContractExe -> Maybe ContractType
contractType exe | exe == contractExe WalletCompanionContract = Just WalletCompanionContract

contractType exe | exe == contractExe ControlContract = Just ControlContract

contractType exe | exe == contractExe FollowContract = Just FollowContract

contractType _ = Nothing
