module Main(main) where

import           Data.Either         (isLeft, isRight)
import qualified Data.Map            as Map
import           Data.Monoid         (Sum (..))
import           Hedgehog            (Property, forAll, property)
import qualified Hedgehog
import qualified Hedgehog.Gen        as Gen
import qualified Hedgehog.Range      as Range
import           Lens.Micro
import           Lens.Micro.Extras   (view)
import           Test.Tasty
import           Test.Tasty.Hedgehog (testProperty)

import           Wallet.Emulator
import           Wallet.Generators   (Mockchain (..))
import qualified Wallet.Generators   as Gen
import           Wallet.UTXO         (unitValidationData)
import qualified Wallet.UTXO.Index   as Index

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "all tests" [
    testGroup "UTXO model" [
        testProperty "initial transaction is valid" initialTxnValid,
        testProperty "compute UTxO of trivial blockchain" utxo,
        testProperty "validate transaction" txnValid
        ],
    testGroup "UTXO index" [
        testProperty "create an index of transactions" txnIndex,
        testProperty "use the index to validate transactions" txnIndexValid
        ],
    testGroup "traces" [
        testProperty "accept valid txn" validTrace,
        testProperty "reject invalid txn" invalidTrace,
        testProperty "notify wallet" notifyWallet
        ],
    testGroup "Etc." [
        testProperty "splitVal" splitVal
        ]
    ]

initialTxnValid :: Property
initialTxnValid = property $ do
    (i, _) <- forAll $ Gen.genInitialTransaction Gen.generatorModel
    Gen.assertValid i Gen.emptyChain

utxo :: Property
utxo = property $ do
    Mockchain block o <- forAll Gen.genMockchain
    Hedgehog.assert (unspentOutputs [block] == o)

txnValid :: Property
txnValid = property $ do
    (m, txn) <- forAll genChainTxn
    Gen.assertValid txn m

txnIndex :: Property
txnIndex = property $ do
    (m, txn) <- forAll genChainTxn
    let (result, st) = Gen.runTrace m $ blockchainActions >> simpleTrace txn
    Hedgehog.assert (Index.initialise (emChain st) == emIndex st)

txnIndexValid :: Property
txnIndexValid = property $ do
    (m, txn) <- forAll genChainTxn
    let (result, st) = Gen.runTrace m blockchainActions
        idx = emIndex st
    Hedgehog.assert (Right True == Index.runLookup (Index.validTxIndexed unitValidationData txn) idx)

-- | Submit a transaction to the blockchain and assert that it has been
--   validated
simpleTrace :: Tx -> Trace ()
simpleTrace txn = do
    [txn'] <- walletAction (Wallet 1) $ submitTxn txn
    block <- blockchainActions
    assertion $ isValidated txn'

validTrace :: Property
validTrace = property $ do
    (m, txn) <- forAll genChainTxn
    let (result, st) = Gen.runTrace m $ blockchainActions >> simpleTrace txn
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == emTxPool st)

invalidTrace :: Property
invalidTrace = property $ do
    (m, txn) <- forAll genChainTxn
    let invalidTxn = txn { txFee = 0 }
        (result, st) = Gen.runTrace m $ simpleTrace invalidTxn
    Hedgehog.assert (isLeft result)
    Hedgehog.assert ([] == emTxPool st)

splitVal :: Property
splitVal = property $ do
    i <- forAll $ Gen.int $ Range.linear 1 (100000 :: Int)
    n <- forAll $ Gen.int $ Range.linear 1 100
    vs <- forAll $ Gen.splitVal n i
    Hedgehog.assert $ sum vs == i
    Hedgehog.assert $ length vs <= n

notifyWallet :: Property
notifyWallet = property $ do
    let w = Wallet 1
    (e, EmulatorState{ emWalletState = st }) <- forAll
        $ Gen.runTraceOn Gen.generatorModel
        $ blockchainActions >>= walletNotifyBlock w
    let ttl = Map.lookup w st
    Hedgehog.assert $ (getSum . foldMap Sum . view ownAddresses <$> ttl) == Just 100000

genChainTxn :: Hedgehog.MonadGen m => m (Mockchain, Tx)
genChainTxn = do
    m <- Gen.genMockchain
    txn <- Gen.genValidTransaction m
    pure (m, txn)

