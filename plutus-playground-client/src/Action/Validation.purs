module Actions.Validation (actionIsValid) where

import Data.Array as Array
import Data.Lens (view)
import Playground.Types (ContractCall(..), SimulatorWallet)
import Prelude ((==), (&&), (<<<))
import Schema.Types (FormArgument)
import Validation (isValid)
import Wallet.Emulator.Wallet (Wallet)
import Wallets.Lenses (_simulatorWalletWallet, _walletId)

actionIsValid :: Array SimulatorWallet -> ContractCall FormArgument -> Boolean
actionIsValid simulatorWallets simulatorAction = actionWalletsExist simulatorAction && isValid simulatorAction
  where
  walletExists :: Wallet -> Boolean
  walletExists wallet =
    Array.any
      (\simulatorWallet -> view _walletId wallet == view (_simulatorWalletWallet <<< _walletId) simulatorWallet)
      simulatorWallets

  actionWalletsExist :: ContractCall FormArgument -> Boolean
  actionWalletsExist (AddBlocks _) = true -- because there is no wallet to check for in the first place

  actionWalletsExist (AddBlocksUntil _) = true -- ditto

  actionWalletsExist (CallEndpoint a@{ caller }) = walletExists caller

  actionWalletsExist (PayToWallet a@{ sender, recipient }) = walletExists sender && walletExists recipient
