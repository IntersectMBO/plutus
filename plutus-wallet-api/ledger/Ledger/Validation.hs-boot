module Ledger.Validation where

import {-# SOURCE #-} Ledger.Scripts

data PendingTxIn' w
type PendingTxIn = PendingTxIn' (Maybe (ValidatorHash, RedeemerHash))
type PendingTxInScript = PendingTxIn' (ValidatorHash, RedeemerHash)
data PendingTx' i
type PendingTx = PendingTx' PendingTxInScript
