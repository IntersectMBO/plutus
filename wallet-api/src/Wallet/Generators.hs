{-# LANGUAGE RecordWildCards #-}
module Wallet.Generators(
    -- * Mockchain
    Mockchain(..),
    genMockchain,
    genMockchain',
    emptyChain,
    GeneratorModel(..),
    generatorModel,
    -- * Transactions
    FeeEstimator(..),
    constantFee,
    genValidTransaction,
    genValidTransaction',
    genInitialTransaction,
    -- * Assertions
    assertValid,
    -- * Etc.
    Wallet.Generators.runTrace,
    splitVal
    ) where

import           Data.Bifunctor  (Bifunctor (..))
import           Data.Map        (Map)
import qualified Data.Map        as Map
import           Data.Maybe      (fromMaybe)
import qualified Data.Set        as Set
import           GHC.Stack       (HasCallStack)
import           Hedgehog
import qualified Hedgehog.Gen    as Gen
import qualified Hedgehog.Range  as Range

import           Wallet.Emulator as Emulator

data GeneratorModel = GeneratorModel {
    -- | Max. number of outputs for the initial transaction
    gmNumOutputs     :: Int,
    -- | Value created at the beginning of the blockchain
    gmInitialBalance :: Value
    } deriving Show

-- | A generator model with some sensible defaults
generatorModel :: GeneratorModel
generatorModel = GeneratorModel {
    gmNumOutputs = 2,
    gmInitialBalance = 100000
    }

-- | Estimate a transaction fee based on the number of its inputs and outputs.
newtype FeeEstimator = FeeEstimator { estimateFee :: Int -> Int -> Value }

-- | A constant fee for all transactions
constantFee :: Value -> FeeEstimator
constantFee = FeeEstimator . const . const

-- | Blockchain for testing the emulator implementation and traces.
--
--   To avoid having to rely on functions from the implementation of
--   wallet-api (in particular, `Wallet.UTXO.unspentOutputs`) we note the
--   unspent outputs of the chain when it is first created.
data Mockchain = Mockchain {
    mockchainBlockchain :: Blockchain,
    mockchainUtxo       :: Map TxOutRef' TxOut'
    } deriving Show

-- | The empty mockchain
emptyChain :: Mockchain
emptyChain = Mockchain [] Map.empty

-- | Generate a mockchain
--
--   TODO: Generate more than 1 txn
genMockchain' :: MonadGen m
    => GeneratorModel
    -> m Mockchain
genMockchain' gm = do
    (txn, ot) <- genInitialTransaction gm
    let txId = hashTx txn
    pure Mockchain {
        mockchainBlockchain = [[txn]],
        mockchainUtxo = Map.fromList $ first (TxOutRef txId) <$> zip [0..] ot
        }

-- | Generate a mockchain using the default [[GeneratorModel]]
--
genMockchain :: MonadGen m => m Mockchain
genMockchain = genMockchain' generatorModel

-- | A transaction with no inputs that forges some value (to be used at the
--   beginning of a blockchain)
genInitialTransaction :: MonadGen m
    => GeneratorModel
    -> m (Tx, [TxOut'])
genInitialTransaction GeneratorModel{..} = do
    vls <- splitVal gmNumOutputs gmInitialBalance
    let o = simpleOutput <$> vls
    pure (Tx {
        txInputs = Set.empty,
        txOutputs = o,
        txForge = gmInitialBalance,
        txFee = 0
        }, o)

-- | Generate a valid transaction, using the unspent outputs provided.
--   Fails if the there are no unspent outputs, or if the total value
--   of the unspent outputs is smaller than the minimum fee (1)
genValidTransaction :: MonadGen m
    => Mockchain
    -> m Tx
genValidTransaction = genValidTransaction' (constantFee 1)

-- | Generate a valid transaction, using the unspent outputs provided.
--   Fails if the there are no unspent outputs, or if the total value
--   of the unspent outputs is smaller than the estimated fee.
genValidTransaction' :: MonadGen m
    => FeeEstimator
    -> Mockchain
    -> m Tx
genValidTransaction' f (Mockchain bc ops) = do
    -- Take a random number of UTXO from the input
    nUtxo <- if Map.null ops
                then Gen.discard
                else Gen.int (Range.linear 1 (Map.size ops))
    let inputs = simpleInput . fst <$> (take nUtxo $ Map.toList ops)
        totalVal = sum (map (fromMaybe 0 . value bc . txInRef) inputs)
        fee = estimateFee f (length inputs) 3
    if fee < totalVal
        then do
            outVals <- splitVal 3 (totalVal - fee)
            pure Tx {
                    txInputs = Set.fromList inputs,
                    txOutputs = simpleOutput <$> outVals,
                    txForge = 0,
                    txFee = fee }
        else Gen.discard

-- | Assert that a transaction is valid in a chain
assertValid :: (MonadTest m, HasCallStack)
    => Tx
    -> Mockchain
    -> m ()
assertValid tx (Mockchain chain _) = Hedgehog.assert (validTx tx chain)

-- | Run an emulator trace on a mockchain
runTrace ::
    Mockchain
    -> Trace a
    -> (Either AssertionError a, EmulatorState)
runTrace (Mockchain chain _) = Emulator.runTrace chain

-- | Split a value into max. n positive-valued parts such that the sum of the
--   parts equals the original value.
splitVal :: (MonadGen m, Integral n) => Int -> n -> m [n]
splitVal mx init = go 0 0 [] where
    go i c l =
        if i >= pred mx
        then pure $ (init - c) : l
        else do
            v <- Gen.integral (Range.linear 1 $ init - c)
            if v + c == init
            then pure $ v : l
            else go (succ i) (v + c) (v : l)
