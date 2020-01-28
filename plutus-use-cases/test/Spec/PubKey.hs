module Spec.PubKey(tests) where

import           Control.Monad                                   (void)

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Test
import           Language.PlutusTx.Lattice
import qualified Ledger
import qualified Ledger.Ada                                      as Ada
import           Wallet.Emulator                                 (walletPubKey)

import           Language.PlutusTx.Coordination.Contracts.PubKey (pubKeyContract)

import           Test.Tasty

w1 :: Wallet
w1 = Wallet 1

theContract :: Contract BlockchainActions ContractError ()
theContract = do
  txin <- pubKeyContract (Ledger.pubKeyHash $ walletPubKey w1) (Ada.lovelaceValueOf 10)
  void $ submitTx $ mustSpendInput txin

tests :: TestTree
tests = testGroup "pubkey"
  [ checkPredicate "works like a public key output"
      theContract
      (walletFundsChange w1 mempty /\ assertDone w1 (const True) "pubkey contract not done")
      (handleBlockchainEvents (Wallet 1))
  ]
