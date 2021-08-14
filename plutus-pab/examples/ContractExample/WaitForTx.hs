{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}

module ContractExample.WaitForTx (
    waitForTx
    ) where

import           Ledger          (TxId)
import           Plutus.Contract (Contract, ContractError, EmptySchema, awaitTxConfirmed, logInfo)

waitForTx :: TxId -> Contract () EmptySchema ContractError ()
waitForTx txid = do
    logInfo @String $ "Waiting for transaction " <> show txid
    awaitTxConfirmed txid
    logInfo @String "CONFIRMED"
