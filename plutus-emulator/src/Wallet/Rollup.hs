{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TemplateHaskell  #-}

module Wallet.Rollup
    ( doAnnotateBlockchain
    ) where

import           Control.Lens             (assign, ifoldr, makeLenses, over, use, view)
import           Control.Lens.Combinators (itraverse)
import           Control.Monad.Except     (MonadError, throwError)
import           Control.Monad.State      (StateT, evalStateT)
import qualified Data.ByteString.Lazy     as BSL
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import qualified Data.Set                 as Set
import           Data.Text                (Text)
import qualified Data.Text                as Text
import           GHC.Generics             (Generic)
import           Language.PlutusTx.Monoid (inv)
import           Ledger                   (Tx (Tx), TxId (TxId), TxIn (TxIn), TxOut (TxOut), Value, getTxId, outValue,
                                           txInRef, txOutRefId, txOutRefIdx, txOutValue, txOutputs)
import qualified Ledger.Tx                as Tx
import           Wallet.Rollup.Types      (AnnotatedTx (AnnotatedTx), BeneficialOwner,
                                           DereferencedInput (DereferencedInput, refersTo), SequenceId (SequenceId),
                                           balances, dereferencedInputs, sequenceId, slotIndex, toBeneficialOwner, tx,
                                           txId, txIndex)

data TxKey =
    TxKey
        { _txKeyTxId        :: BSL.ByteString
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
txInputKey TxIn {txInRef} =
    TxKey
        { _txKeyTxId = getTxId $ txOutRefId txInRef
        , _txKeyTxOutRefIdx = txOutRefIdx txInRef
        }

annotateTransaction ::
       MonadError Text m => SequenceId -> Tx -> StateT Rollup m AnnotatedTx
annotateTransaction sequenceId tx@Tx {txOutputs} = do
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
            (Set.toList $ view Tx.inputs tx)
    let txIdOf@(TxId txId) = Tx.txId tx
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
                ((over outValue inv . refersTo <$> dereferencedInputs) <>
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
            { sequenceId
            , txId = txIdOf
            , tx
            , dereferencedInputs
            , balances = newBalances
            }

annotateChainSlot ::
       MonadError Text m => Int -> [Tx] -> StateT Rollup m [AnnotatedTx]
annotateChainSlot slotIndex =
    itraverse (\txIndex -> annotateTransaction SequenceId {..})

annotateBlockchain ::
       MonadError Text m => [[Tx]] -> StateT Rollup m [[AnnotatedTx]]
annotateBlockchain = fmap reverse . itraverse annotateChainSlot . reverse

doAnnotateBlockchain :: MonadError Text m => [[Tx]] -> m [[AnnotatedTx]]
doAnnotateBlockchain blockchain =
    evalStateT
        (annotateBlockchain blockchain)
        (Rollup {_previousOutputs = Map.empty, _rollingBalances = Map.empty})
