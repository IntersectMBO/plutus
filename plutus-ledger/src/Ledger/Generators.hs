{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
-- | Generators for constructing blockchains and transactions for use in property-based testing.
module Ledger.Generators(
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
    genAda,
    genValue,
    genValueNonNegative,
    genSizedByteString,
    genSizedByteStringExact,
    genTokenName,
    splitVal,
    validateMockchain,
    signAll
    ) where

import           Data.Bifunctor            (Bifunctor (..))
import           Data.Foldable             (fold, foldl')
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Maybe                (isNothing)
import           Data.Set                  (Set)
import qualified Data.Set                  as Set
import           GHC.Stack                 (HasCallStack)
import           Hedgehog
import qualified Hedgehog.Gen              as Gen
import qualified Hedgehog.Range            as Range
import qualified Language.PlutusTx.Prelude as P
import qualified Ledger.Ada                as Ada
import qualified Ledger.Index              as Index
import qualified Ledger.Interval           as Interval
import qualified Ledger.Value              as Value

import           Ledger

-- | Attach signatures of all known private keys to a transaction.
signAll :: Tx -> Tx
signAll tx = foldl' (flip addSignature) tx knownPrivateKeys

-- | The parameters for the generators in this module.
data GeneratorModel = GeneratorModel {
    gmInitialBalance :: Map PubKey Value,
    -- ^ Value created at the beginning of the blockchain.
    gmPubKeys        :: Set PubKey
    -- ^ Public keys that are to be used for generating transactions.
    } deriving Show

-- | A generator model with some sensible defaults.
generatorModel :: GeneratorModel
generatorModel =
    let vl = Ada.lovelaceValueOf 100000
        pubKeys = toPublicKey <$> knownPrivateKeys

    in
    GeneratorModel
    { gmInitialBalance = Map.fromList $ zip pubKeys (repeat vl)
    , gmPubKeys        = Set.fromList pubKeys
    }

-- | A function that estimates a transaction fee based on the number of its inputs and outputs.
newtype FeeEstimator = FeeEstimator { estimateFee :: Integer -> Integer -> Ada }

-- | Estimate a constant fee for all transactions.
constantFee :: Ada -> FeeEstimator
constantFee = FeeEstimator . const . const

-- | Blockchain for testing the emulator implementation and traces.
--
--   To avoid having to rely on functions from the implementation of
--   plutus-ledger (in particular, 'Ledger.Tx.unspentOutputs') we note the
--   unspent outputs of the chain when it is first created.
data Mockchain = Mockchain {
    mockchainInitialBlock :: Block,
    mockchainUtxo         :: Map TxOutRef TxOut
    } deriving Show

-- | The empty mockchain.
emptyChain :: Mockchain
emptyChain = Mockchain [] Map.empty

-- | Generate a mockchain.
--
--   TODO: Generate more than 1 txn
genMockchain' :: MonadGen m
    => GeneratorModel
    -> m Mockchain
genMockchain' gm = do
    let (txn, ot) = genInitialTransaction gm
        tid = txId txn
    pure Mockchain {
        mockchainInitialBlock = [txn],
        mockchainUtxo = Map.fromList $ first (TxOutRef tid) <$> zip [0..] ot
        }

-- | Generate a mockchain using the default 'GeneratorModel'.
--
genMockchain :: MonadGen m => m Mockchain
genMockchain = genMockchain' generatorModel

-- | A transaction with no inputs that forges some value (to be used at the
--   beginning of a blockchain).
genInitialTransaction ::
       GeneratorModel
    -> (Tx, [TxOut])
genInitialTransaction GeneratorModel{..} =
    let
        o = (uncurry $ flip pubKeyTxOut) <$> Map.toList gmInitialBalance
        t = fold gmInitialBalance
    in (mempty {
        txOutputs = o,
        txForge = t,
        txValidRange = Interval.from 0
        }, o)

-- | Generate a valid transaction, using the unspent outputs provided.
--   Fails if the there are no unspent outputs, or if the total value
--   of the unspent outputs is smaller than the minimum fee (1).
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
genValidTransaction' g f (Mockchain _ ops) = do
    -- Take a random number of UTXO from the input
    nUtxo <- if Map.null ops
                then Gen.discard
                else Gen.int (Range.linear 1 (Map.size ops))
    let ins = Set.fromList $ pubKeyTxIn . fst <$> inUTXO
        inUTXO = take nUtxo $ Map.toList ops
        totalVal = foldl' (+) 0 $ map (Ada.fromValue . txOutValue . snd) inUTXO
    genValidTransactionSpending' g f ins totalVal

genValidTransactionSpending :: MonadGen m
    => Set.Set TxIn
    -> Ada
    -> m Tx
genValidTransactionSpending = genValidTransactionSpending' generatorModel (constantFee 1)

genValidTransactionSpending' :: MonadGen m
    => GeneratorModel
    -> FeeEstimator
    -> Set.Set TxIn
    -> Ada
    -> m Tx
genValidTransactionSpending' g f ins totalVal = do
    let fee = estimateFee f (fromIntegral $ length ins) 3
        numOut = Set.size $ gmPubKeys g
    if fee < totalVal
        then do
            let sz = totalVal - fee
            outVals <- fmap Ada.toValue <$> splitVal numOut sz
            let tx = mempty
                        { txInputs = ins
                        , txOutputs = uncurry pubKeyTxOut <$> zip outVals (Set.toList $ gmPubKeys g)
                        , txFee = Ada.toValue fee
                        }

                -- sign the transaction with all three known wallets
                -- this is somewhat crude (but technically valid)
            pure (signAll tx)
        else Gen.discard

genAda :: MonadGen m => m Ada
genAda = Ada.lovelaceOf <$> Gen.integral (Range.linear 0 (100000 :: Integer))

-- | Generate a 'ByteString s' of up to @s@ bytes.
genSizedByteString :: forall m. MonadGen m => Int -> m P.ByteString
genSizedByteString s =
    let range = Range.linear 0 s
    in Gen.bytes range

-- | Generate a 'ByteString s' of exactly @s@ bytes.
genSizedByteStringExact :: forall m. MonadGen m => Int -> m P.ByteString
genSizedByteStringExact s =
    let range = Range.singleton s
    in Gen.bytes range

genTokenName :: MonadGen m => m TokenName
genTokenName = Value.TokenName <$> Gen.utf8 (Range.linear 0 32) Gen.unicode

genValue' :: MonadGen m => Range Integer -> m Value
genValue' valueRange = do
    let
        -- currency symbol is either a validator hash (bytestring of length 32)
        -- or the ada symbol (empty bytestring).
        currency = Gen.choice
                    [ Value.currencySymbol <$> genSizedByteStringExact 32
                    , pure Ada.adaSymbol
                    ]

        -- token is either an arbitrary bytestring or the ada token name
        token   = Gen.choice
                    [ genTokenName
                    , pure Ada.adaToken
                    ]
        sngl      = Value.singleton <$> currency <*> token <*> Gen.integral valueRange

        -- generate values with no more than 5 elements to avoid the tests
        -- taking too long (due to the map-as-list-of-kv-pairs implementation)
        maxCurrencies = 5

    numValues <- Gen.int (Range.linear 0 maxCurrencies)
    fold <$> traverse (const sngl) [0 .. numValues]

-- | Generate a 'Value' with a value range of @minBound .. maxBound@.
genValue :: MonadGen m => m Value
genValue = genValue' $ fromIntegral <$> Range.linearBounded @Int

-- | Generate a 'Value' with a value range of @0 .. maxBound@.
genValueNonNegative :: MonadGen m => m Value
genValueNonNegative = genValue' $ fromIntegral <$> Range.linear @Int 0 maxBound

-- | Assert that a transaction is valid in a chain.
assertValid :: (MonadTest m, HasCallStack)
    => Tx
    -> Mockchain
    -> m ()
assertValid tx mc = Hedgehog.assert $ isNothing $ validateMockchain mc tx

-- | Validate a transaction in a mockchain.
validateMockchain :: Mockchain -> Tx -> Maybe Index.ValidationError
validateMockchain (Mockchain blck _) tx = either Just (const Nothing) result where
    h      = 1
    idx    = Index.initialise [blck]
    result = Index.runValidation (Index.validateTransaction h tx) idx

-- | Split a value into max. n positive-valued parts such that the sum of the
--   parts equals the original value.
splitVal :: (MonadGen m, Integral n) => Int -> n -> m [n]
splitVal _  0     = pure []
splitVal mx init' = go 0 0 [] where
    go i c l =
        if i >= pred mx
        then pure $ (init' - c) : l
        else do
            v <- Gen.integral (Range.linear 1 $ init' - c)
            if v + c == init'
            then pure $ v : l
            else go (succ i) (v + c) (v : l)
