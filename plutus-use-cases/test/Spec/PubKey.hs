{-# LANGUAGE TypeApplications #-}
module Spec.PubKey(tests, pubKeyTrace) where

import           Control.Monad           (void)
import qualified Data.Map                as Map

import qualified Ledger
import qualified Ledger.Ada              as Ada
import           Ledger.Constraints      (ScriptLookups (..))
import qualified Ledger.Constraints      as Constraints
import           Ledger.Scripts          (unitRedeemer)
import           Ledger.Typed.Scripts    as Scripts
import           Plutus.Contract
import           Plutus.Contract.Test
import qualified Plutus.Trace.Emulator   as Trace

import           Plutus.Contracts.PubKey (PubKeyError, pubKeyContract)

import           Test.Tasty

w1 :: Wallet
w1 = Wallet 1

theContract :: Contract () BlockchainActions PubKeyError ()
theContract = do
  (txOutRef, txOutTx, pkInst) <- pubKeyContract (Ledger.pubKeyHash $ walletPubKey w1) (Ada.lovelaceValueOf 10)
  let lookups = ScriptLookups
                  { slMPS = Map.empty
                  , slTxOutputs = Map.singleton txOutRef txOutTx
                  , slOtherScripts = Map.singleton (Scripts.scriptAddress pkInst) (Scripts.validatorScript pkInst)
                  , slOtherData = Map.empty
                  , slTypedValidator = Nothing
                  , slOwnPubkey = Nothing
                  }
  void $ submitTxConstraintsWith @Scripts.Any lookups (Constraints.mustSpendScriptOutput txOutRef unitRedeemer)

tests :: TestTree
tests = testGroup "pubkey"
  [ checkPredicate "works like a public key output"
      (walletFundsChange w1 mempty .&&. assertDone theContract (Trace.walletInstanceTag w1) (const True) "pubkey contract not done")
      pubKeyTrace
  ]

-- | Use 'pubKeyContract' to create a script output that works like a
--   public key output, requiring only the right signature on the spending
--   transaction. Then spend the script output.
pubKeyTrace :: Trace.EmulatorTrace ()
pubKeyTrace = do
    _ <- Trace.activateContractWallet w1 theContract
    void $ Trace.waitNSlots 2
