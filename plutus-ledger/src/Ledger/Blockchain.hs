{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
module Ledger.Blockchain (
    Block,
    Blockchain,
    Context(..),
    transaction,
    out,
    value,
    unspentOutputsTx,
    spentOutputs,
    unspentOutputs,
    datumTxo,
    updateUtxo,
    txOutPubKey,
    pubKeyTxo,
    validValuesTx
    ) where

import           Control.Monad            (join)
import           Data.List                (find)
import           Data.Map                 (Map)
import qualified Data.Map                 as Map

import           Plutus.V1.Ledger.Crypto
import           Plutus.V1.Ledger.Scripts
import           Plutus.V1.Ledger.Tx
import           Plutus.V1.Ledger.TxId
import           Plutus.V1.Ledger.Value   (Value)

-- | A block on the blockchain. This is just a list of transactions which
-- successfully validate following on from the chain so far.
type Block = [Tx]
-- | A blockchain, which is just a list of blocks, starting with the newest.
type Blockchain = [Block]

-- | Lookup a transaction in a 'Blockchain' by its id.
transaction :: Blockchain -> TxId -> Maybe Tx
transaction bc tid = find p $ join bc where
    p tx = tid == txId tx

-- | Determine the unspent output that an input refers to
out :: Blockchain -> TxOutRef -> Maybe TxOut
out bc o = do
    t <- transaction bc (txOutRefId o)
    let i = txOutRefIdx o
    if fromIntegral (length (txOutputs t)) <= i
        then Nothing
        else Just $ txOutputs t !! fromIntegral i

-- | Determine the unspent value that a transaction output refers to.
value :: Blockchain -> TxOutRef -> Maybe Value
value bc o = txOutValue <$> out bc o

-- | Determine the data script that a transaction output refers to.
datumTxo :: Blockchain -> TxOutRef -> Maybe DatumHash
datumTxo bc o = txOutDatum =<< out bc o

-- | Determine the public key that locks a transaction output, if there is one.
pubKeyTxo :: Blockchain -> TxOutRef -> Maybe PubKeyHash
pubKeyTxo bc o = out bc o >>= txOutPubKey

-- | The unspent transaction outputs of the ledger as a whole.
unspentOutputs :: Blockchain -> Map TxOutRef TxOut
unspentOutputs = foldr updateUtxo Map.empty . join
