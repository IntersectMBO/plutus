{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Messages where
-- TRIM TO HERE
-- Contract endpoints that generate different kinds of errors for the log:
-- logAMessage produces a log message from a wallet
-- submitInvalidTxn submits an invalid txn which should result in a
-- "Validation failed" message throwWalletAPIError throws an error from
-- a wallet (client)
import           Language.PlutusTx.Prelude

import qualified Data.Map                  as Map
import qualified Data.Set                  as Set
import           Data.Text                 (Text)

import           Ledger
import qualified Ledger.Ada                as Ada
import           Ledger.Validation
import           Playground.Contract
import           Wallet

logAMessage :: MonadWallet m => m ()
logAMessage = logMsg "wallet log"

submitInvalidTxn :: MonadWallet m => m ()
submitInvalidTxn = do
    logMsg "Preparing to submit an invalid transaction"
    let tx = Tx
            { txInputs = Set.empty
            , txOutputs = []
            , txForge = Ada.adaValueOf 2
            , txFee = 0
            , txValidRange = defaultSlotRange
            , txSignatures = Map.empty
            }
    submitTxn tx

throwWalletAPIError :: MonadWallet m => Text -> m ()
throwWalletAPIError = throwOtherError

$(mkFunctions ['logAMessage, 'submitInvalidTxn, 'throwWalletAPIError])
