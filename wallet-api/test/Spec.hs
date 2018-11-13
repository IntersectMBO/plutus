module Main(main) where

import           Control.Lens
import           Control.Monad       (void)
import           Data.Either         (isLeft, isRight)
import           Data.Foldable       (traverse_)
import qualified Data.Map            as Map
import           Data.Monoid         (Sum (..))
import           Hedgehog            (Property, forAll, property)
import qualified Hedgehog
import qualified Hedgehog.Gen        as Gen
import qualified Hedgehog.Range      as Range
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
        testProperty "notify wallet" notifyWallet,
        testProperty "react to blockchain events" eventTrace,
        testProperty "watch funds at an address" notifyWallet
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
    Hedgehog.assert (Right () == Index.runValidation (Index.validateTransaction 0 txn) idx)

-- | Submit a transaction to the blockchain and assert that it has been
--   validated
simpleTrace :: Tx -> Trace EmulatedWalletApi ()
simpleTrace txn = do
    [txn'] <- walletAction (Wallet 1) $ submitTxn txn
    block <- blockchainActions
    assertIsValidated txn'

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
    Hedgehog.assert $ (getSum . foldMap Sum . view ownFunds <$> ttl) == Just initialBalance

eventTrace :: Property
eventTrace = property $ do
    let w = Wallet 1
    (e, EmulatorState{ emWalletState = st }) <- forAll
        $ Gen.runTraceOn Gen.generatorModel
        $ do
            blockchainActions >>= walletNotifyBlock w
            let mkPayment = BlockchainAction $ \_ _ -> payToPubKey 100 (PubKey 2)
                trigger = blockHeightT (GEQ 3)

            -- schedule the `mkPayment` action to run when block height 3 is
            -- reached.
            b1 <- walletAction (Wallet 1) $ register trigger mkPayment
            walletNotifyBlock w b1

            -- advance the clock to trigger `mkPayment`
            addBlocks 2 >>= traverse_ (walletNotifyBlock w)
            void (blockchainActions >>= walletNotifyBlock w)
    let ttl = Map.lookup w st

    -- if `mkPayment` was run then the funds of wallet 1 should be reduced by 100
    Hedgehog.assert $ (getSum . foldMap Sum . view ownFunds <$> ttl) == Just (initialBalance - 100)

watchFundsAtAddress :: Property
watchFundsAtAddress = property $ do
    let w = Wallet 1
        pkTarget = PubKey 2
    (e, EmulatorState{ emWalletState = st }) <- forAll
        $ Gen.runTraceOn Gen.generatorModel
        $ do
            blockchainActions >>= walletNotifyBlock w
            let mkPayment = BlockchainAction $ \_ _ -> payToPubKey 100 (PubKey 2)
                t1 = blockHeightT (Interval 3 4)
                t2 = fundsAtAddressT (pubKeyAddress pkTarget) (GEQ 1)
            walletNotifyBlock w =<<
                (walletAction (Wallet 1) $ do
                    register t1 mkPayment
                    register t2 mkPayment)

            -- after 3 blocks, t1 should fire, triggering the first payment of 100 to PubKey 2
            -- after 4 blocks, t2 should fire, triggering the second payment of 100
            addBlocks 3 >>= traverse_ (walletNotifyBlock w)
            void (blockchainActions >>= walletNotifyBlock w)
    let ttl = Map.lookup w st
    Hedgehog.assert $ (getSum . foldMap Sum . view ownFunds <$> ttl) == Just (initialBalance - 200)


genChainTxn :: Hedgehog.MonadGen m => m (Mockchain, Tx)
genChainTxn = do
    m <- Gen.genMockchain
    txn <- Gen.genValidTransaction m
    pure (m, txn)

initialBalance :: Value
initialBalance = 100000
