{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TemplateHaskell  #-}

module Playground.Rollup
    ( doAnnotateBlockchain
    ) where

import           Codec.Serialise.Class    (Serialise)
import           Control.Lens             (assign, ifoldr, makeLenses, over, traversed, use)
import           Control.Lens.Combinators (itraverse)
import           Control.Monad.Except     (MonadError, throwError)
import           Control.Monad.State      (StateT, evalStateT)
import           Crypto.Hash              (Digest, SHA256)
import qualified Data.Aeson.Extras        as JSON
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import           Data.Set                 (Set)
import qualified Data.Set                 as Set
import           Data.Text                (Text)
import qualified Data.Text                as Text
import           GHC.Generics             (Generic)
import           Language.PlutusTx.Monoid (inv)
import           Ledger                   (DataScript, PubKey, Tx, TxId, TxIdOf (TxIdOf), TxIn, TxInOf (TxInOf), TxOut,
                                           TxOutOf (TxOutOf), TxOutRefOf, TxOutType (PayToPubKey, PayToScript), Value,
                                           getDataScript, getPubKey, getTxId, outValue, txInRef, txInputs, txOutRefId,
                                           txOutRefIdx, txOutType, txOutValue, txOutputs)
import           Playground.Types         (AnnotatedTx (AnnotatedTx), SequenceId (SequenceId), balances,
                                           dereferencedInputs, involvedAddresses, involvedTransactions, sequenceId,
                                           slotIndex, tx, txId, txIndex)

data TxKey =
    TxKey
        { _txKeyTxId        :: Digest SHA256
        , _txKeyTxOutRefIdx :: Integer
        }
    deriving (Show, Eq, Ord, Generic)

data Rollup =
    Rollup
        { _previousOutputs :: Map TxKey TxOut
        , _rollingBalances :: Map TxOutType Value
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
annotateTransaction sequenceId (txIdOf@(TxIdOf txId), tx) = do
    cPreviousOutputs <- use previousOutputs
    cRollingBalances <- use rollingBalances
    dereferencedInputs <-
        traverse
            (\txIn ->
                 let key = txInputKey txIn
                  in case Map.lookup key cPreviousOutputs of
                         Just txOut -> pure txOut
                         Nothing ->
                             throwError $
                             Text.pack $
                             "Could not find referenced transaction: " <>
                             show key)
            (Set.toList (txInputs tx))
    let newOutputs =
            ifoldr
                (\outputIndex ->
                     Map.insert
                         TxKey
                             { _txKeyTxId = txId
                             , _txKeyTxOutRefIdx = fromIntegral outputIndex
                             })
                cPreviousOutputs
                (txOutputs tx)
        newBalances =
            foldr
                sumAccounts
                cRollingBalances
                (over (traversed . outValue) inv dereferencedInputs <>
                 txOutputs tx)
        sumAccounts :: TxOut -> Map TxOutType Value -> Map TxOutType Value
        sumAccounts TxOutOf {txOutType, txOutValue} =
            Map.alter sumBalances txOutType
          where
            sumBalances :: Maybe Value -> Maybe Value
            sumBalances Nothing         = Just txOutValue
            sumBalances (Just oldValue) = Just (oldValue <> txOutValue)
        involvedAddresses =
            foldMap getAddresses (dereferencedInputs <> txOutputs tx)
        involvedTransactions = foldMap getTxIds (txInputs tx)
    assign previousOutputs newOutputs
    assign rollingBalances newBalances
    pure $
        AnnotatedTx
            { sequenceId
            , txId = txIdOf
            , tx
            , dereferencedInputs
            , balances = newBalances
            , involvedAddresses
            , involvedTransactions
            }

class HasAddresses a where
    getAddresses :: a -> Set Text

instance HasAddresses (TxOutOf a) where
    getAddresses = getAddresses . txOutType

instance HasAddresses TxOutType where
    getAddresses (PayToScript dataScript) = getAddresses dataScript
    getAddresses (PayToPubKey pubKey)     = getAddresses pubKey

instance HasAddresses PubKey where
    getAddresses = Set.singleton . JSON.encodeSerialise . getPubKey

instance HasAddresses DataScript where
    getAddresses = Set.singleton . JSON.encodeSerialise . getDataScript

class HasTxIds a where
    getTxIds :: a -> Set Text

instance Serialise a => HasTxIds (TxInOf a) where
    getTxIds = getTxIds . txInRef

instance Serialise a => HasTxIds (TxOutRefOf a) where
    getTxIds = getTxIds . txOutRefId

instance Serialise a => HasTxIds (TxIdOf a) where
    getTxIds = Set.singleton . JSON.encodeSerialise . getTxId

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
