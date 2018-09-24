module Main(main) where

import           Control.Monad.Operational  as Op
import           Control.Monad.State        (runState)
import           Control.Monad.Trans.Except (runExceptT)
import           Data.Either                (isLeft, isRight)
import           Generators                 (Mockchain (..))
import qualified Generators                 as Gen
import           Hedgehog                   (Property, forAll, property)
import qualified Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog        (testProperty)

import           Wallet.Emulator

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "all tests" [
    testGroup "UTXO model" [
        testProperty "initial transaction is valid" initialTxnValid,
        testProperty "compute UTxO of trivial blockchain" utxo,
        testProperty "validate transaction" txnValid
        ],
    testGroup "traces" [
        testProperty "accept valid txn" validTrace,
        testProperty "reject invalid txn" invalidTrace
        ]
    ]

initialTxnValid :: Property
initialTxnValid = property $ do
    (i, _) <- forAll Gen.genInitialTransaction
    Hedgehog.assert (validTx i [])

utxo :: Property
utxo = property $ do
    Mockchain chain o <- forAll Gen.genMockchain
    Hedgehog.assert (unspentOutputs chain == o)

txnValid :: Property
txnValid = property $ do
    Mockchain chain o <- forAll Gen.genMockchain
    txn <- forAll $ Gen.genValidTransaction chain o
    Hedgehog.assert (validTx txn chain)

-- | Submit a transaction to the blockchain and assert that it has been valided
simpleTrace :: Tx -> Trace ()
simpleTrace txn = do
    [txn'] <- Op.singleton $ WalletAction (Wallet 1) $ submitTxn txn
    block <- Op.singleton BlockchainActions
    Op.singleton $ Assertion $ isValidated txn'

validTrace :: Property
validTrace = property $ do
    Mockchain chain o <- forAll Gen.genMockchain
    txn <- forAll $ Gen.genValidTransaction chain o
    let trace = simpleTrace txn
        emState = emulatorState chain
        (result, st) = runState (runExceptT $ process trace) emState
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == emTxPool st)

invalidTrace :: Property
invalidTrace = property $ do
    Mockchain chain o <- forAll Gen.genMockchain
    txn <- forAll $ Gen.genValidTransaction chain o
    let invalidTxn = txn { txFee = 0 }
        trace = simpleTrace invalidTxn
        emState = emulatorState chain
        (result, st) = runState (runExceptT $ process trace) emState
    Hedgehog.assert (isLeft result)
    Hedgehog.assert ([] == emTxPool st)

