{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TemplateHaskell    #-}
module Ledger.Blockchain (
    OnChainTx(..),
    _Valid,
    _Invalid,
    Block,
    Blockchain,
    Context(..),
    eitherTx,
    consumableInputs,
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
    validValuesTx,
    ) where

import           Codec.Serialise          (Serialise)
import           Control.DeepSeq          (NFData)
import           Control.Lens             (makePrisms, view)
import           Control.Monad            (join)
import           Data.Aeson               (FromJSON, ToJSON)
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import           Data.Monoid              (First (..))
import qualified Data.Set                 as Set
import           GHC.Generics             (Generic)

import           Plutus.V1.Ledger.Crypto
import           Plutus.V1.Ledger.Scripts
import           Plutus.V1.Ledger.Tx
import           Plutus.V1.Ledger.TxId
import           Plutus.V1.Ledger.Value   (Value)

-- | A transaction on the blockchain.
-- Invalid transactions are still put on the chain to be able to collect fees.
data OnChainTx = Invalid Tx | Valid Tx
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON, Serialise, NFData)
-- | A block on the blockchain. This is just a list of transactions
-- following on from the chain so far.
type Block = [OnChainTx]
-- | A blockchain, which is just a list of blocks, starting with the newest.
type Blockchain = [Block]

eitherTx :: (Tx -> r) -> (Tx -> r) -> OnChainTx -> r
eitherTx ifInvalid _ (Invalid tx) = ifInvalid tx
eitherTx _ ifValid (Valid tx)     = ifValid tx

consumableInputs :: OnChainTx -> Set.Set TxIn
consumableInputs = eitherTx (view inputsFees) (view inputs <> view inputsFees)

-- | Lookup a transaction in a 'Blockchain' by its id.
transaction :: Blockchain -> TxId -> Maybe OnChainTx
transaction bc tid = getFirst . foldMap (foldMap p) $ bc where
    p tx = if tid == eitherTx txId txId tx then First (Just tx) else mempty

-- | Determine the unspent output that an input refers to
out :: Blockchain -> TxOutRef -> Maybe TxOut
out bc o = do
    Valid t <- transaction bc (txOutRefId o)
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
unspentOutputs = foldr (eitherTx updateUtxoFees updateUtxo) Map.empty . join

makePrisms ''OnChainTx
