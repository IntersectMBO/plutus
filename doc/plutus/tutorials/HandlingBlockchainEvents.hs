{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
module HandlingBlockchainEvents() where

import           Data.List.NonEmpty (NonEmpty)
import           Ledger
import           Plutus.ChainIndex  (ChainIndexTx, TxStatus)
import           Plutus.Contract    as Contract

-- BLOCK0
{-| Wait until one or more unspent outputs are produced at an address.
-}
awaitUtxoProduced ::
  forall w s e .
  (AsContractError e)
  => Address
  -> Contract w s e (NonEmpty ChainIndexTx)
-- BLOCK1
awaitUtxoProduced = Contract.awaitUtxoProduced
-- BLOCK2
{-| Wait until the UTXO has been spent, returning the transaction that spends it.
-}
awaitUtxoSpent ::
  forall w s e.
  (AsContractError e)
  => TxOutRef
  -> Contract w s e ChainIndexTx
-- BLOCK3
awaitUtxoSpent = Contract.awaitUtxoSpent
-- BLOCK4
-- | Wait for the status of a transaction to change
awaitTxStatusChange ::
  forall w s e.
  (AsContractError e)
  => TxId
  -> Contract w s e TxStatus
-- BLOCK5
awaitTxStatusChange = Contract.awaitTxStatusChange
