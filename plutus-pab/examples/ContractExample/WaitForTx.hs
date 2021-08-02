{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}

module ContractExample.WaitForTx (
    waitForTx
    , WaitForTxSchema
    ) where

import           Ledger          (TxId)
import           Plutus.Contract (ContractError, Endpoint, Promise, awaitTxConfirmed, endpoint, logInfo)

type WaitForTxSchema = Endpoint "tx-id" TxId

waitForTx :: Promise () WaitForTxSchema ContractError ()
waitForTx = endpoint @"tx-id" $ \txid -> do
    logInfo @String $ "Waiting for transaction " <> show txid
    awaitTxConfirmed txid
    logInfo @String "CONFIRMED"
