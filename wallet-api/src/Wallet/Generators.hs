{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE RecordWildCards  #-}
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
    genValidTransactionSpending,
    genValidTransactionSpending',
    genInitialTransaction,
    -- * Assertions
    assertValid,
    -- * Etc.
    genValue,
    Wallet.Generators.runTrace,
    runTraceOn,
    splitVal,
    validateMockchain
    ) where

import           Data.Bifunctor              (Bifunctor (..))
import           Data.Map                    (Map)
import qualified Data.Map                    as Map
import           Data.Maybe                  (catMaybes, isNothing)
import           Data.Monoid                 (Sum (..))
import           Data.Set                    (Set)
import qualified Data.Set                    as Set
import           GHC.Stack                   (HasCallStack)
import           Hedgehog
import qualified Hedgehog.Gen                as Gen
import qualified Hedgehog.Range              as Range
import qualified Ledger.Interval             as Interval
import qualified Ledger.Index                as Index

import           Ledger
import qualified Wallet.API      as W
import           Wallet.Emulator as Emulator

data GeneratorModel = GeneratorModel {
    gmInitialBalance :: Map PubKey Value,
    -- ^ Value created at the beginning of the blockchain
    gmPubKeys        :: Set PubKey
    -- ^ Public keys that are to be used for generating transactions
    } deriving Show

-- | A generator model with some sensible defaults
generatorModel :: GeneratorModel
generatorModel = GeneratorModel {
    gmInitialBalance = Map.fromList $ first PubKey <$> zip [1..5] (repeat 100000),
    gmPubKeys        = Set.fromList $ PubKey <$> [1..5]
    }

-- | Estimate a transaction fee based on the number of its inputs and outputs.
newtype FeeEstimator = FeeEstimator { estimateFee :: Int -> Int -> Value }

-- | A constant fee for all transactions
constantFee :: Value -> FeeEstimator
constantFee = FeeEstimator . const . const

-- | Blockchain for testing the emulator implementation and traces.
--
--   To avoid having to rely on functions from the implementation of
--   wallet-api (in particular, `Ledger.Types.unspentOutputs`) we note the
--   unspent outputs of the chain when it is first created.
data Mockchain = Mockchain {
    mockchainInitialBlock :: Block,
    mockchainUtxo         :: Map TxOutRef TxOut
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
    let (txn, ot) = genInitialTransaction gm
        txId = hashTx txn
    pure Mockchain {
        mockchainInitialBlock = [txn],
        mockchainUtxo = Map.fromList $ first (TxOutRefOf txId) <$> zip [0..] ot
        }

-- | Generate a mockchain using the default [[GeneratorModel]]
--
genMockchain :: MonadGen m => m Mockchain
genMockchain = genMockchain' generatorModel

-- | A transaction with no inputs that forges some value (to be used at the
--   beginning of a blockchain)
genInitialTransaction ::
       GeneratorModel
    -> (Tx, [TxOut])
genInitialTransaction GeneratorModel{..} =
    let
        o = (uncurry $ flip pubKeyTxOut) <$> Map.toList gmInitialBalance
        t = getSum $ foldMap Sum gmInitialBalance
    in (Tx {
        txInputs = Set.empty,
        txOutputs = o,
        txForge = t,
        txFee = 0,
        txValidRange = W.intervalFrom 0
        }, o)

-- | Generate a valid transaction, using the unspent outputs provided.
--   Fails if the there are no unspent outputs, or if the total value
--   of the unspent outputs is smaller than the minimum fee (1)
genValidTransaction :: MonadGen m
    => Mockchain
    -> m Tx
genValidTransaction = genValidTransaction' generatorModel (constantFee 1)

-- | Generate a valid transaction, using the unspent outputs provided.
--   Fails if the there are no unspent outputs, or if the total value
--   of the unspent outputs is smaller than the estimated fee.
genValidTransaction' :: MonadGen m
    => GeneratorModel
    -> FeeEstimator
    -> Mockchain
    -> m Tx
genValidTransaction' g f (Mockchain bc ops) = do
    -- Take a random number of UTXO from the input
    nUtxo <- if Map.null ops
                then Gen.discard
                else Gen.int (Range.linear 1 (Map.size ops))
    let ins = Set.fromList
                    $ uncurry pubKeyTxIn . second mkSig
                    <$> (catMaybes
                        $ traverse (pubKeyTxo [bc]) . (di . fst) <$> inUTXO)
        inUTXO = take nUtxo $ Map.toList ops
        totalVal = sum (map (txOutValue . snd) inUTXO)
        di a = (a, a)
        mkSig (PubKey i) = Signature i
    genValidTransactionSpending' g f ins totalVal

genValidTransactionSpending :: MonadGen m
    => Set.Set TxIn
    -> Value
    -> m Tx
genValidTransactionSpending = genValidTransactionSpending' generatorModel (constantFee 1)

genValidTransactionSpending' :: MonadGen m
    => GeneratorModel
    -> FeeEstimator
    -> Set.Set TxIn
    -> Value
    -> m Tx
genValidTransactionSpending' g f ins totalVal = do
    let fee = estimateFee f (length ins) 3
        numOut = Set.size $ gmPubKeys g
    if fee < totalVal
        then do
            outVals <- splitVal numOut (totalVal - fee)
            pure Tx {
                    txInputs = ins,
                    txOutputs = uncurry pubKeyTxOut <$> zip outVals (Set.toList $ gmPubKeys g),
                    txForge = 0,
                    txFee = fee,
                    txValidRange = $$(Interval.always) }
        else Gen.discard

genValue :: MonadGen m => m Value
genValue = Value <$> Gen.int (Range.linear 0 (100000 :: Int))

-- | Assert that a transaction is valid in a chain
assertValid :: (MonadTest m, HasCallStack)
    => Tx
    -> Mockchain
    -> m ()
assertValid tx mc = Hedgehog.assert $ isNothing $ validateMockchain mc tx

-- | Validate a transaction in a mockchain
validateMockchain :: Mockchain -> Tx -> Maybe Index.ValidationError
validateMockchain (Mockchain blck _) tx = either Just (const Nothing) result where
    h      = lastSlot [blck]
    idx    = Index.initialise [blck]
    result = Index.runValidation (Index.validateTransaction h tx) idx

-- | Run an emulator trace on a mockchain
runTrace ::
    Mockchain
    -> Trace MockWallet a
    -> (Either AssertionError a, EmulatorState)
runTrace (Mockchain ch _) = Emulator.runTraceTxPool ch

-- | Run an emulator trace on a mockchain generated by the model
runTraceOn :: MonadGen m
    => GeneratorModel
    -> Trace MockWallet a
    -> m (Either AssertionError a, EmulatorState)
runTraceOn gm t = flip Wallet.Generators.runTrace t <$> genMockchain' gm

-- | Split a value into max. n positive-valued parts such that the sum of the
--   parts equals the original value.
splitVal :: (MonadGen m, Integral n) => Int -> n -> m [n]
splitVal mx init' = go 0 0 [] where
    go i c l =
        if i >= pred mx
        then pure $ (init' - c) : l
        else do
            v <- Gen.integral (Range.linear 1 $ init' - c)
            if v + c == init'
            then pure $ v : l
            else go (succ i) (v + c) (v : l)
