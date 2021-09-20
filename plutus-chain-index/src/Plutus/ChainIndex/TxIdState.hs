{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}

module Plutus.ChainIndex.TxIdState(
    increaseDepth
    , initialStatus
    , transactionStatus
    , fromTx
    , fromBlock
    , rollback
    , chainConstant
    , dropOlder
    ) where

import           Control.Lens                ((^.))
import           Data.FingerTree             ((|>))
import qualified Data.FingerTree             as FT
import qualified Data.Map                    as Map
import           Data.Monoid                 (Last (..), Sum (..))
import           Ledger                      (OnChainTx, TxId, eitherTx)
import           Plutus.ChainIndex.Tx        (ChainIndexTx (..), ChainIndexTxOutputs (..), citxOutputs, citxTxId)
import           Plutus.ChainIndex.Types     (BlockNumber (..), Depth (..), Point (..), RollbackState (..), Tip (..),
                                              TxConfirmedState (..), TxIdState (..), TxStatus, TxStatusFailure (..),
                                              TxValidity (..))
import           Plutus.ChainIndex.UtxoState (RollbackFailed (..), RollbackResult (..), UtxoIndex, UtxoState (..),
                                              rollbackWith, tip, utxoState, viewTip)


-- | The 'TxStatus' of a transaction right after it was added to the chain
initialStatus :: OnChainTx -> TxStatus
initialStatus tx =
  TentativelyConfirmed 0 (eitherTx (const TxInvalid) (const TxValid) tx) ()

-- | Increase the depth of a tentatively confirmed transaction
increaseDepth :: TxStatus -> TxStatus
increaseDepth (TentativelyConfirmed d s ())
  | d < succ chainConstant = TentativelyConfirmed (d + 1) s ()
  | otherwise              = Committed s ()
increaseDepth e            = e

-- TODO: Configurable!
-- | The depth (in blocks) after which a transaction cannot be rolled back anymore
chainConstant :: Depth
chainConstant = Depth 8

-- | Drop everything older than 'BlockNumber' in the index.
dropOlder :: (Monoid a)
          => BlockNumber
          -> UtxoIndex a
          -> UtxoIndex a
dropOlder targetBlock idx = FT.dropUntil (blockEqTip targetBlock . tip . snd) idx

blockEqTip :: BlockNumber -> Tip -> Bool
blockEqTip blockTarget (Tip _ _ blockAtTip) = blockTarget == blockAtTip
blockEqTip _                  TipAtGenesis  = False

-- | Given the current block, compute the status for the given transaction by
-- checking to see if it has been deleted.
transactionStatus :: BlockNumber -> TxIdState -> TxId -> Either TxStatusFailure TxStatus
transactionStatus currentBlock txIdState txId
  = case (confirmed, deleted) of
       (Nothing, _)      -> Right Unknown

       (Just TxConfirmedState{blockAdded=Last (Just block'), validity=Last (Just validity')}, Nothing) ->
         if isCommitted block'
            then Right $ Committed validity' ()
            else Right $ newStatus block' validity' ()

       (Just TxConfirmedState{timesConfirmed=confirms, blockAdded=Last (Just block'), validity=Last (Just validity')}, Just deletes) ->
         if confirms > deletes
            -- It's fine, it's confirmed
            then Right $ newStatus block' validity' ()
            -- Otherwise, throw an error if it looks deleted but we're too far
            -- into the future.
            else if isCommitted block'
                    -- Illegal - We can't roll this transaction back.
                    then Left $ InvalidRollbackAttempt currentBlock txId txIdState
                    else Right Unknown

       _ -> Left $ TxIdStateInvalid currentBlock txId txIdState
    where
      -- A block is committed at least 'chainConstant' number of blocks
      -- has elapsed since the block was added.
      isCommitted addedInBlock = currentBlock > addedInBlock + fromIntegral chainConstant

      newStatus block' validity' =
        if isCommitted block'
           then Committed validity'
           else TentativelyConfirmed (Depth $ fromIntegral $ currentBlock - block') validity'

      confirmed = Map.lookup txId (txnsConfirmed txIdState)
      deleted   = Map.lookup txId (txnsDeleted txIdState)


fromBlock :: Tip -> [ChainIndexTx] -> UtxoState TxIdState
fromBlock tip_ transactions =
  UtxoState
    { _usTxUtxoData = foldMap (fromTx $ tipBlockNo tip_) transactions
    , _usTip = tip_
    }

validityFromChainIndex :: ChainIndexTx -> TxValidity
validityFromChainIndex tx =
  case tx ^. citxOutputs of
    InvalidTx -> TxInvalid
    ValidTx _ -> TxValid

fromTx :: BlockNumber -> ChainIndexTx -> TxIdState
fromTx blockNumber tx =
  TxIdState
    { txnsConfirmed =
        Map.singleton
          (tx ^. citxTxId)
          (TxConfirmedState { timesConfirmed = Sum 1
                            , blockAdded = Last . Just $ blockNumber
                            , validity = Last . Just $ validityFromChainIndex tx })
    , txnsDeleted = mempty
    }

rollback :: Point
         -> UtxoIndex TxIdState
         -> Either RollbackFailed (RollbackResult TxIdState)
rollback = rollbackWith markDeleted
  where
    markDeleted before deleted =
      let oldTxIdState = _usTxUtxoData (utxoState deleted)
          newTxIdState = TxIdState
                            { txnsConfirmed = mempty
                            -- All the transactions that were confirmed in the deleted
                            -- section are now deleted.
                            , txnsDeleted = 1 <$ txnsConfirmed oldTxIdState
                            }
          newUtxoState = UtxoState (oldTxIdState <> newTxIdState) (viewTip before)
      in before |> newUtxoState
