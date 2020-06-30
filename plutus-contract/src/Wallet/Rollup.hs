{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE RecordWildCards  #-}

module Wallet.Rollup
    ( doAnnotateBlockchain
    , initialState
    , annotateBlockchain
    , Rollup
    ) where

import           Control.Lens             (assign, ifoldr, over, use, view)
import           Control.Lens.Combinators (itraverse)
import           Control.Monad.State      (StateT, evalStateT)
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import qualified Data.Set                 as Set
import           Language.PlutusTx.Monoid (inv)
import           Ledger                   (Tx (Tx), TxIn (TxIn), TxOut (TxOut), Value, outValue, txInRef, txOutRefId,
                                           txOutRefIdx, txOutValue, txOutputs)
import qualified Ledger.Tx                as Tx
import           Wallet.Rollup.Types

------------------------------------------------------------
txInputKey :: TxIn -> TxKey
txInputKey TxIn {txInRef} =
    TxKey
        { _txKeyTxId = txOutRefId txInRef
        , _txKeyTxOutRefIdx = txOutRefIdx txInRef
        }

annotateTransaction ::
       Monad m => SequenceId -> Tx -> StateT Rollup m AnnotatedTx
annotateTransaction sequenceId tx@Tx {txOutputs} = do
    cPreviousOutputs <- use previousOutputs
    cRollingBalances <- use rollingBalances
    dereferencedInputs <-
        traverse
            (\txIn ->
                 let key = txInputKey txIn
                  in case Map.lookup key cPreviousOutputs of
                         Just txOut -> pure $ DereferencedInput txIn txOut
                         Nothing    -> pure $ InputNotFound key)
            (Set.toList $ view Tx.inputs tx)
    let txId = Tx.txId tx
        newOutputs =
            ifoldr
                (\outputIndex ->
                     Map.insert
                         TxKey
                             { _txKeyTxId = txId
                             , _txKeyTxOutRefIdx = fromIntegral outputIndex
                             })
                cPreviousOutputs
                txOutputs
        newBalances =
            foldr
                sumAccounts
                cRollingBalances
                ((over outValue inv . refersTo <$> filter isFound dereferencedInputs) <>
                 txOutputs)
        sumAccounts ::
               TxOut -> Map BeneficialOwner Value -> Map BeneficialOwner Value
        sumAccounts txOut@TxOut {txOutValue} =
            Map.alter sumBalances (toBeneficialOwner txOut)
          where
            sumBalances :: Maybe Value -> Maybe Value
            sumBalances Nothing         = Just txOutValue
            sumBalances (Just oldValue) = Just (oldValue <> txOutValue)
    assign previousOutputs newOutputs
    assign rollingBalances newBalances
    pure $
        AnnotatedTx
            {sequenceId, txId, tx, dereferencedInputs, balances = newBalances}

annotateChainSlot :: Monad m => Int -> [Tx] -> StateT Rollup m [AnnotatedTx]
annotateChainSlot slotIndex =
    itraverse (\txIndex -> annotateTransaction SequenceId {..})

annotateBlockchain :: Monad m => [[Tx]] -> StateT Rollup m [[AnnotatedTx]]
annotateBlockchain = fmap reverse . itraverse annotateChainSlot . reverse

initialState :: Rollup
initialState =
    Rollup {_previousOutputs = Map.empty, _rollingBalances = Map.empty}

doAnnotateBlockchain :: Monad m => [[Tx]] -> m [[AnnotatedTx]]
doAnnotateBlockchain blockchain =
    evalStateT (annotateBlockchain blockchain) initialState
