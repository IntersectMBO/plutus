{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module Main(main) where


import           Control.Lens
import           Control.Monad              (void)
import           Control.Monad.Trans.Except (runExcept)
import qualified Data.Aeson                 as JSON
import qualified Data.Aeson.Extras          as JSON
import qualified Data.Aeson.Internal        as Aeson
import qualified Data.ByteString            as BSS
import qualified Data.ByteString.Lazy       as BSL
import           Data.Either                (isLeft, isRight)
import           Data.Foldable              (fold, foldl', traverse_)
import           Data.List                  (sort)
import qualified Data.Map                   as Map
import           Data.Monoid                (Sum (..))
import qualified Data.Set                   as Set
import           Data.String                (IsString (fromString))
import           Data.String                (IsString (fromString))
import           Hedgehog                   (Property, forAll, property)
import qualified Hedgehog
import qualified Hedgehog.Gen               as Gen
import qualified Hedgehog.Range             as Range
import qualified Language.PlutusTx.Builtins as Builtins
import qualified Language.PlutusTx.Prelude  as PlutusTx
import           Language.PlutusTx.AssocMap as AssocMap
import           Ledger
import qualified Ledger.Ada                 as Ada
import qualified Ledger.Index               as Index
import qualified Ledger.Value               as Value
import           Ledger.Value               (CurrencySymbol, Value (Value))
import           LedgerBytes                as LedgerBytes
import           Test.Tasty
import           Test.Tasty.Hedgehog        (testProperty)
import           Test.Tasty.HUnit           (testCase)
import qualified Test.Tasty.HUnit           as HUnit
import           Wallet
import qualified Wallet.API                 as W
import           Wallet.Emulator.Types
import qualified Wallet.Generators          as Gen
import qualified Wallet.Emulator.Generators          as Gen
import           Wallet.Generators          (Mockchain(Mockchain))
import qualified Wallet.Graph

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "all tests" [
    testGroup "UTXO model" [
        testProperty "compute UTxO of trivial blockchain" utxo,
        testProperty "validate transaction" txnValid,
        testProperty "validate transaction when it can be validated" txnValidFrom,
        testProperty "update UTXO set after each transaction" txnUpdateUtxo
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
        testProperty "watch funds at an address" notifyWallet,
        testProperty "log script validation failures" invalidScript,
        testProperty "payToPubkey" payToPubKeyScript,
        testProperty "payToPubkey-2" payToPubKeyScript2
        ],
    testGroup "Etc." [
        testProperty "selectCoin" selectCoinProp,
        testProperty "txnFlows" txnFlowsTest
        ]
    ]

wallet1, wallet2, wallet3 :: Wallet
wallet1 = Wallet 1
wallet2 = Wallet 2
wallet3 = Wallet 3

pubKey1, pubKey2, pubKey3 :: PubKey
pubKey1 = walletPubKey wallet1
pubKey2 = walletPubKey wallet2
pubKey3 = walletPubKey wallet3

utxo :: Property
utxo = property $ do
    Mockchain block o <- forAll Gen.genMockchain
    Hedgehog.assert (unspentOutputs [block] == o)

txnValid :: Property
txnValid = property $ do
    (m, txn) <- forAll genChainTxn
    Gen.assertValid txn m

txnValidFrom :: Property
txnValidFrom = property $ do
    (e, _) <- forAll $ Gen.runTraceOn Gen.generatorModel validFromTransaction
    Hedgehog.assert $ isRight e

selectCoinProp :: Property
selectCoinProp = property $ do
    inputs <- forAll $ zip [1..] <$> Gen.list (Range.linear 1 100) Gen.genValueNonNegative
    target <- forAll Gen.genValueNonNegative
    let result = runExcept (selectCoin inputs target)
    case result of
        Left _ ->
            Hedgehog.assert $ not $ (fold $ snd <$> inputs) `Value.geq` target
        Right (ins, change) ->
            Hedgehog.assert $ (fold $ snd <$> ins) == (target `Value.plus` change)

-- | Submits a transaction that is valid in the future, then adds a number of
--   slots, then verifies that the transaction has been validated.
validFromTransaction :: Trace MockWallet ()
validFromTransaction = do
    let [w1, w2] = [wallet1, wallet2]
        updateAll = processPending >>= walletsNotifyBlock [w1, w2]
        five = Ada.adaValueOf 5
    updateAll

    -- Set the validation interval to (5, 5] for the
    -- transaction generated by payToPublicKey_
    -- so that the transaction can be validated only during slot 5
    let range = W.singleton 5

    walletAction w1 $ payToPublicKey_ range five pubKey2

    -- Add some blocks so that the transaction is validated
    addBlocks 50 >>= traverse_ (walletsNotifyBlock [w1, w2])
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, initialBalance `Value.minus` five),
        (w2, initialBalance `Value.plus` five)]

txnIndex :: Property
txnIndex = property $ do
    (m, txn) <- forAll genChainTxn
    let (result, st) = Gen.runTrace m $ processPending >> simpleTrace txn
    Hedgehog.assert (Index.initialise (_chainNewestFirst st) == _index st)

txnIndexValid :: Property
txnIndexValid = property $ do
    (m, txn) <- forAll genChainTxn
    let (result, st) = Gen.runTrace m processPending
        idx = _index st
    Hedgehog.assert (isRight (Index.runValidation (Index.validateTransaction 0 txn) idx))


-- | Submit a transaction to the blockchain and assert that it has been
--   validated
simpleTrace :: Tx -> Trace MockWallet ()
simpleTrace txn = do
    txn' <- head <$> (walletAction wallet1 $ signTxAndSubmit_ txn)
    block <- processPending
    assertIsValidated txn'

txnUpdateUtxo :: Property
txnUpdateUtxo = property $ do
    (Mockchain m _, txn) <- forAll genChainTxn
    let idx  = Index.initialise [m]
        slot = 1

        -- Validate a pool that contains `txn` twice. It should succeed the
        -- first and fail the second time
        ValidatedBlock [t1] [e1, e2] [] _ = validateBlock slot idx [txn, txn]
        txId = hashTx txn
    Hedgehog.assert (t1 == txn)
    Hedgehog.assert $ case (e1, e2) of
        (TxnValidate i1, TxnValidationFail txi (Index.TxOutRefNotFound _)) -> i1 == txId && txi == txId
        _                                                                  -> False

validTrace :: Property
validTrace = property $ do
    (m, txn) <- forAll genChainTxn
    let (result, st) = Gen.runTrace m $ processPending >> simpleTrace txn
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == _txPool st)

invalidTrace :: Property
invalidTrace = property $ do
    (m, txn) <- forAll genChainTxn
    let invalidTxn = txn { txFee = 0 }
        (result, st) = Gen.runTrace m $ simpleTrace invalidTxn
    Hedgehog.assert (isLeft result)
    Hedgehog.assert ([] == _txPool st)
    Hedgehog.assert (not (null $ _emulatorLog st))
    Hedgehog.assert (case _emulatorLog st of
        SlotAdd _ : TxnValidationFail _ _ : _ -> True
        _                                     -> False)

invalidScript :: Property
invalidScript = property $ do
    (m, txn1) <- forAll genChainTxn

    -- modify one of the outputs to be a script output
    index <- forAll $ Gen.int (Range.linear 0 ((length $ txOutputs txn1) -1))
    let scriptTxn = txn1 & outputs . element index %~ \o -> scriptTxOut (txOutValue o) failValidator unitData
    Hedgehog.annotateShow (scriptTxn)
    let outToSpend = (txOutRefs scriptTxn) !! index
    let totalVal = Ada.fromValue $ txOutValue (fst outToSpend)

    -- try and spend the script output
    invalidTxn <- forAll $ Gen.genValidTransactionSpending (Set.fromList [scriptTxIn (snd outToSpend) failValidator unitRedeemer]) totalVal
    Hedgehog.annotateShow (invalidTxn)

    let (result, st) = Gen.runTrace m $ do
            processPending
            -- we need to sign scriptTxn again because it has been modified
            -- note that although 'scriptTxn' is submitted by wallet 1, it
            -- may spend outputs belonging to one of the other two wallets.
            -- So we can't use 'signTxAndSubmit_' (because it would only attach
            -- wallet 1's signatures). Instead, we get all the wallets'
            -- signatures with 'signAll'.
            walletAction wallet1 $ submitTxn (Gen.signAll scriptTxn)
            processPending
            walletAction wallet1 $ signTxAndSubmit_ invalidTxn
            processPending

    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == _txPool st)
    Hedgehog.assert (not (null $ _emulatorLog st))
    Hedgehog.annotateShow (_emulatorLog st)
    Hedgehog.assert $ case _emulatorLog st of
        SlotAdd{} : TxnValidationFail _ (ScriptFailure ["I always fail everything"]) : _
            -> True
        _
            -> False

    where
        failValidator :: ValidatorScript
        failValidator = ValidatorScript $ $$(compileScript [|| validator ||])
        validator :: () -> () -> PendingTx -> Bool
        validator _ _ _ = PlutusTx.traceErrorH "I always fail everything"


txnFlowsTest :: Property
txnFlowsTest = property $ do
    (_, e) <- forAll $ Gen.runTraceOn Gen.generatorModel pubKeyTransactions
    let chain = _chainNewestFirst e
        numTx = length $ fold chain
        flows = Wallet.Graph.txnFlows [] chain
        -- there should be at least one link per tx
        -- plus some for the unspent outputs
    Hedgehog.assert (length flows > numTx)

notifyWallet :: Property
notifyWallet = property $ do
    let w = wallet1
    (e, _) <- forAll
        $ Gen.runTraceOn Gen.generatorModel
        $ do
            processPending >>= walletNotifyBlock w
            assertOwnFundsEq w initialBalance

    Hedgehog.assert $ isRight e

eventTrace :: Property
eventTrace = property $ do
    let w = wallet1
    (e, _) <- forAll
        $ Gen.runTraceOn Gen.generatorModel
        $ do
            processPending >>= walletNotifyBlock w
            let mkPayment =
                    EventHandler $ \_ -> payToPublicKey_ W.always (Ada.adaValueOf 100) pubKey2
                trigger = slotRangeT (W.intervalFrom 3)

            -- schedule the `mkPayment` action to run when slot 3 is
            -- reached.
            b1 <- walletAction wallet1 $ register trigger mkPayment
            walletNotifyBlock w b1

            -- advance the clock to trigger `mkPayment`
            addBlocks 2 >>= traverse_ (walletNotifyBlock w)
            void (processPending >>= walletNotifyBlock w)
            assertOwnFundsEq w (initialBalance `Value.minus` Ada.adaValueOf 100)

    Hedgehog.assert $ isRight e

payToPubKeyScript2 :: Property
payToPubKeyScript2 = property $ do
    let [w1, w2, w3] = [wallet1, wallet2, wallet3]
        updateAll = processPending >>= walletsNotifyBlock [w1, w2, w3]
        payment1 = initialBalance `Value.minus` Ada.adaValueOf 1
        payment2 = initialBalance `Value.plus` Ada.adaValueOf 1
    (e, _) <- forAll
        $ Gen.runTraceOn Gen.generatorModel
        $ do
            updateAll
            walletAction wallet1 $ payToPublicKey_ W.always payment1 pubKey2
            updateAll
            walletAction wallet2 $ payToPublicKey_ W.always payment2 pubKey3
            updateAll
            walletAction wallet3 $ payToPublicKey_ W.always payment2 pubKey1
            updateAll
            walletAction wallet1 $ payToPublicKey_ W.always (Ada.adaValueOf 2) pubKey2
            updateAll
            traverse_ (uncurry assertOwnFundsEq) [
                (w1, initialBalance),
                (w2, initialBalance),
                (w3, initialBalance)]
    Hedgehog.assert $ isRight e

pubKeyTransactions :: Trace MockWallet ()
pubKeyTransactions = do
    let [w1, w2, w3] = [wallet1, wallet2, wallet3]
        updateAll = processPending >>= walletsNotifyBlock [w1, w2, w3]
        five = Ada.adaValueOf 5
    updateAll
    walletAction wallet1 $ payToPublicKey_ W.always five pubKey2
    updateAll
    walletAction wallet2 $ payToPublicKey_ W.always five pubKey3
    updateAll
    walletAction wallet3 $ payToPublicKey_ W.always five pubKey1
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, initialBalance),
        (w2, initialBalance),
        (w3, initialBalance)]

payToPubKeyScript :: Property
payToPubKeyScript = property $ do
    (e, _) <- forAll $ Gen.runTraceOn Gen.generatorModel pubKeyTransactions
    Hedgehog.assert $ isRight e

watchFundsAtAddress :: Property
watchFundsAtAddress = property $ do
    let w = wallet1
        pkTarget = pubKey2
    (e, EmulatorState{ _walletStates = st }) <- forAll
        $ Gen.runTraceOn Gen.generatorModel
        $ do
            processPending >>= walletNotifyBlock w
            let mkPayment =
                    EventHandler $ \_ -> payToPublicKey_ W.always (Ada.adaValueOf 100) pubKey2
                t1 = slotRangeT (W.interval 3 4)
                t2 = fundsAtAddressGtT (pubKeyAddress pkTarget) Value.zero
            walletNotifyBlock w =<<
                (walletAction wallet1 $ do
                    register t1 mkPayment
                    register t2 mkPayment)

            -- after 3 blocks, t1 should fire, triggering the first payment of 100 to PubKey 2
            -- after 4 blocks, t2 should fire, triggering the second payment of 100
            addBlocks 3 >>= traverse_ (walletNotifyBlock w)
            void (processPending >>= walletNotifyBlock w)
            assertOwnFundsEq w (initialBalance `Value.minus` Ada.adaValueOf 200)

    Hedgehog.assert $ isRight e

genChainTxn :: Hedgehog.MonadGen m => m (Mockchain, Tx)
genChainTxn = do
    m <- Gen.genMockchain
    txn <- Gen.genValidTransaction m
    pure (m, txn)


initialBalance :: Value
initialBalance = Ada.adaValueOf 100000
