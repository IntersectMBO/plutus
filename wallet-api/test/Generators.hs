module Generators(
    -- * Mockchain
    Mockchain(..),
    genMockchain,
    -- * Transactions
    genInitialTransaction,
    genValidTransaction
    ) where

import           Data.Map              (Map)
import qualified Data.Map              as Map
import           Data.Maybe            (fromMaybe)
import           Hedgehog
import qualified Hedgehog.Gen          as Gen
import qualified Hedgehog.Range        as Range

import           Wallet.Emulator.Types
import           Wallet.UTXO

-- | Blockchain for testing the emulator implementation and traces.
--
--   To avoid having to rely on functions from the implementation of
--   wallet-api (in particular, `Wallet.UTXO.unspentOutputs`) we note the
--   unspent outputs of the chain when it is first created.
data Mockchain = Mockchain {
    mockchainBlockchain :: Blockchain,
    mockchainUtxo       :: Map TxOutRef TxOut
    } deriving Show

-- | Generate a mockchain
--
--   TODO: Generate more than 1 txn
genMockchain :: MonadGen m
    => m Mockchain
genMockchain = do
    (txn, ot) <- genInitialTransaction
    let txId = hashTx txn
    pure Mockchain {
        mockchainBlockchain = [[txn]],
        mockchainUtxo = Map.singleton (TxOutRef txId 0) ot
        }

-- | A transaction with no inputs that forges some value (to be used at the
--   beginning of a blockchain)
genInitialTransaction :: MonadGen m
    => m (Tx, TxOut)
genInitialTransaction = do
    vl <- Value <$> Gen.integral (Range.linear 1 1000000)
    let o = simpleOutput vl
    pure (Tx {
        txInputs = [],
        txOutputs = [o],
        txForge = vl,
        txFee = 0
        }, o)

-- | Generate a valid transaction, using the unspent outputs provided.
--   Fails if the there are no unspent outputs, or if the total value
--   of the unspent outputs is smaller than the minimum fee (1)
genValidTransaction :: MonadGen m
    => Blockchain
    -> Map TxOutRef TxOut
    -> m Tx
genValidTransaction bc ops = do
    -- Take a random number of UTXO from the input
    nUtxo <- if Map.null ops
             then Gen.discard
             else Gen.int (Range.linear 1 (Map.size ops))
    let inputs = fmap simpleInput
            $ take nUtxo
            $ fst
            <$> Map.toList ops
        totalVal = sum (map (fromMaybe 0 . value bc . txInRef) inputs)
        minFee = 1
    fee <- Gen.integral (Range.linear minFee totalVal)
    if fee < totalVal
        then pure Tx {
                txInputs = inputs,
                txOutputs = [simpleOutput $ totalVal - fee],
                txForge = 0,
                txFee = fee
            }
        else Gen.discard

