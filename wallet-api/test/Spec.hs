module Main(main) where

import           Control.Monad.Operational  as Op
import           Control.Monad.State        (runState)
import           Control.Monad.Trans.Except (runExceptT)
import           Data.Either                (isLeft, isRight)
import           Generators                 (Mockchain (..))
import qualified Generators                 as Gen
import           Hedgehog                   (Property, forAll, property)
import qualified Hedgehog
import qualified Hedgehog.Gen               as Gen
import qualified Hedgehog.Range             as Range
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
    Mockchain chain o <- forAll Gen.genMockchain
    Hedgehog.assert (unspentOutputs chain == o)

txnValid :: Property
txnValid = property $ do
    m <- forAll Gen.genMockchain
    txn <- forAll $ Gen.genValidTransaction m
    Gen.assertValid txn m

-- | Submit a transaction to the blockchain and assert that it has been 
--   validated
simpleTrace :: Tx -> Trace ()
simpleTrace txn = do
    [txn'] <- Op.singleton $ WalletAction (Wallet 1) $ submitTxn txn
    block <- Op.singleton BlockchainActions
    Op.singleton $ Assertion $ isValidated txn'

validTrace :: Property
validTrace = property $ do
    m <- forAll Gen.genMockchain
    txn <- forAll $ Gen.genValidTransaction m
    let (result, st) = Gen.runTrace m $ simpleTrace txn
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == emTxPool st)

invalidTrace :: Property
invalidTrace = property $ do
    m <- forAll Gen.genMockchain
    txn <- forAll $ Gen.genValidTransaction m
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