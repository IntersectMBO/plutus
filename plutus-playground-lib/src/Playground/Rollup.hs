{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TemplateHaskell  #-}

module Playground.Rollup
    ( doAnnotateBlockchain
    ) where

import           Control.Lens             (assign, ifoldr, makeLenses, over, use)
import           Control.Lens.Combinators (itraverse)
import           Control.Monad.Except     (MonadError, throwError)
import           Control.Monad.State      (StateT, evalStateT)
import           Crypto.Hash              (Digest, SHA256)
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import qualified Data.Set                 as Set
import           Data.Text                (Text)
import qualified Data.Text                as Text
import           GHC.Generics             (Generic)
import           Language.PlutusTx.Monoid (inv)
import           Ledger                   (Tx (Tx), TxId, TxIdOf (TxIdOf), TxIn, TxInOf (TxInOf), TxOut,
                                           TxOutOf (TxOutOf), Value, getTxId, outValue, txInRef, txInputs, txOutRefId,
                                           txOutRefIdx, txOutValue, txOutputs)
import           Playground.Types         (AnnotatedTx (AnnotatedTx), BeneficialOwner,
                                           DereferencedInput (DereferencedInput, refersTo), SequenceId (SequenceId),
                                           balances, dereferencedInputs, sequenceId, slotIndex, toBeneficialOwner, tx,
                                           txId, txIndex)

data TxKey =
    TxKey
        { _txKeyTxId        :: Digest SHA256
        , _txKeyTxOutRefIdx :: Integer
        }
    deriving (Show, Eq, Ord, Generic)

data Rollup =
    Rollup
        { _previousOutputs :: Map TxKey TxOut
        , _rollingBalances :: Map BeneficialOwner Value
        }
    deriving (Show, Eq, Generic)

makeLenses 'Rollup

------------------------------------------------------------
txInputKey :: TxIn -> TxKey
txInputKey TxInOf {txInRef} =
    TxKey
        { _txKeyTxId = getTxId $ txOutRefId txInRef
        , _txKeyTxOutRefIdx = txOutRefIdx txInRef
        }

annotateTransaction ::
       MonadError Text m
    => SequenceId
    -> (TxId, Tx)
    -> StateT Rollup m AnnotatedTx
annotateTransaction sequenceId (txIdOf@(TxIdOf txId), tx@Tx { txInputs
                                                            , txOutputs
                                                            }) = do
    cPreviousOutputs <- use previousOutputs
    cRollingBalances <- use rollingBalances
    dereferencedInputs <-
        traverse
            (\txIn ->
                 let key = txInputKey txIn
                  in case Map.lookup key cPreviousOutputs of
                         Just txOut -> pure $ DereferencedInput txIn txOut
                         Nothing ->
                             throwError $
                             Text.pack $
                             "Could not find referenced transaction: " <>
                             show key)
            (Set.toList txInputs)
    let newOutputs =
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
                ((over outValue inv . refersTo <$> dereferencedInputs) <>
                 txOutputs)
        sumAccounts ::
               TxOut -> Map BeneficialOwner Value -> Map BeneficialOwner Value
        sumAccounts txOut@TxOutOf {txOutValue} =
            Map.alter sumBalances (toBeneficialOwner txOut)
          where
            sumBalances :: Maybe Value -> Maybe Value
            sumBalances Nothing         = Just txOutValue
            sumBalances (Just oldValue) = Just (oldValue <> txOutValue)
    assign previousOutputs newOutputs
    assign rollingBalances newBalances
    pure $
        AnnotatedTx
            { sequenceId
            , txId = txIdOf
            , tx
            , dereferencedInputs
            , balances = newBalances
            }

annotateChainSlot ::
       MonadError Text m => Int -> [(TxId, Tx)] -> StateT Rollup m [AnnotatedTx]
annotateChainSlot slotIndex =
    itraverse (\txIndex -> annotateTransaction SequenceId {..})

annotateBlockchain ::
       MonadError Text m => [[(TxId, Tx)]] -> StateT Rollup m [[AnnotatedTx]]
annotateBlockchain = fmap reverse . itraverse annotateChainSlot . reverse

doAnnotateBlockchain :: MonadError Text m => [[(TxId, Tx)]] -> m [[AnnotatedTx]]
doAnnotateBlockchain blockchain =
    evalStateT
        (annotateBlockchain blockchain)
        (Rollup {_previousOutputs = Map.empty, _rollingBalances = Map.empty})
