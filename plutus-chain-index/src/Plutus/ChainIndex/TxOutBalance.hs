{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
module Plutus.ChainIndex.TxOutBalance where

import           Control.Lens                (view)
import qualified Data.Map                    as Map
import           Data.Set                    (Set)
import qualified Data.Set                    as Set
import           Ledger                      (TxIn (txInRef), TxOutRef (..))
import           Plutus.ChainIndex.Tx        (ChainIndexTx (..), citxInputs, citxTxId, txOutsWithRef)
import           Plutus.ChainIndex.TxIdState (transactionStatus)
import           Plutus.ChainIndex.Types     (BlockNumber, Point (..), Tip (..), TxIdState, TxOutBalance (..),
                                              TxOutState (..), TxOutStatus, TxStatusFailure (TxOutBalanceStateInvalid),
                                              tobSpentOutputs, tobUnspentOutputs)
import           Plutus.ChainIndex.UtxoState (RollbackFailed, RollbackResult, UtxoIndex,
                                              UtxoState (UtxoState, _usTip, _usTxUtxoData), rollbackWith, usTxUtxoData)

-- | Given the current block, compute the status for the given transaction
-- output by getting the state of the transaction that produced it and checking
-- if the output is spent or unspent.
transactionOutputStatus
  :: BlockNumber
  -- ^ Current block number for inspecting the state of the transaction output
  -> TxIdState
  -- ^ Information on the state of a transaction. Needed for determining its
  -- status.
  -> TxOutBalance
  -- ^ Balance of spent and unspent transaction outputs.
  -> TxOutRef
  -- ^ Target transaction output for inspecting its state.
  -> Either TxStatusFailure TxOutStatus
transactionOutputStatus currentBlock txIdState txOutBalance txOutRef@TxOutRef { txOutRefId } =
  let spentTxOutTxId = Map.lookup txOutRef (_tobSpentOutputs txOutBalance)
      isUnspent = txOutRef `Set.member` _tobUnspentOutputs txOutBalance
      txOutState
          | isUnspent = Just Unspent
          | Just txid <- spentTxOutTxId = Just (Spent txid)
          | Nothing <- spentTxOutTxId = Nothing
   in case txOutState of
        Nothing -> Left $ TxOutBalanceStateInvalid currentBlock txOutRef txOutBalance
        Just s@(Spent txid) -> do
          -- Get the status of the tx which spent the target tx output
          txStatus <- transactionStatus currentBlock txIdState txid
          Right $ fmap (const s) txStatus
        Just s@Unspent -> do
          -- Get the status of the tx which produced the target tx output
          txStatus <- transactionStatus currentBlock txIdState txOutRefId
          Right $ fmap (const s) txStatus

fromTx :: ChainIndexTx -> TxOutBalance
fromTx tx =
    TxOutBalance
        { _tobUnspentOutputs = Set.fromList $ fmap snd $ txOutsWithRef tx
        , _tobSpentOutputs =
          Map.fromSet (const $ view citxTxId tx)
                      $ Set.mapMonotonic txInRef (view citxInputs tx)
        }

-- | Whether a 'TxOutRef' is a member of the UTXO set (ie. unspent)
isUnspentOutput :: TxOutRef -> UtxoState TxOutBalance -> Bool
isUnspentOutput r = Set.member r . unspentOutputs

-- | The UTXO set
unspentOutputs :: UtxoState TxOutBalance -> Set TxOutRef
unspentOutputs = view (usTxUtxoData . tobUnspentOutputs)

-- | Whether a 'TxOutRef' is a member of the spent tx output set.
isSpentOutput :: TxOutRef -> UtxoState TxOutBalance -> Bool
isSpentOutput r = Set.member r . spentOutputs

-- | The spent output set
spentOutputs :: UtxoState TxOutBalance -> Set TxOutRef
spentOutputs = Map.keysSet . view (usTxUtxoData . tobSpentOutputs)

-- | 'UtxoIndex' for a single block
fromBlock :: Tip -> [ChainIndexTx] -> UtxoState TxOutBalance
fromBlock tip_ transactions =
    UtxoState
            { _usTxUtxoData = foldMap fromTx transactions
            , _usTip        = tip_
            }

-- | Perform a rollback on the utxo index
rollback :: Point
         -> UtxoIndex TxOutBalance
         -> Either RollbackFailed (RollbackResult TxOutBalance)
rollback = rollbackWith const
