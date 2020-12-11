{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module Spec.Emulator(tests) where


import           Control.Lens
import           Control.Monad              (void)
import qualified Control.Monad.Freer        as Eff
import qualified Control.Monad.Freer.Error  as E
import           Control.Monad.Freer.Extras
import           Control.Monad.Freer.Log    (logMessageContent)
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
import           Hedgehog                   (Property, forAll, property)
import qualified Hedgehog
import qualified Hedgehog.Gen               as Gen
import qualified Hedgehog.Range             as Range
import qualified Language.PlutusTx          as PlutusTx
import           Language.PlutusTx.AssocMap as AssocMap
import qualified Language.PlutusTx.Builtins as Builtins
import qualified Language.PlutusTx.Numeric  as P
import qualified Language.PlutusTx.Prelude  as PlutusTx
import           Ledger
import qualified Ledger.Ada                 as Ada
import           Ledger.Generators          (Mockchain (Mockchain))
import qualified Ledger.Generators          as Gen
import qualified Ledger.Index               as Index
import           Ledger.Typed.Scripts       (wrapValidator)
import           Ledger.Value               (CurrencySymbol, Value (Value))
import qualified Ledger.Value               as Value
import           LedgerBytes                as LedgerBytes
import           Test.Tasty
import           Test.Tasty.HUnit           (testCase)
import qualified Test.Tasty.HUnit           as HUnit
import           Test.Tasty.Hedgehog        (testProperty)
import           Wallet
import qualified Wallet.API                 as W
import qualified Wallet.Emulator.Chain      as Chain
import qualified Wallet.Emulator.Generators as Gen
import           Wallet.Emulator.MultiAgent (EmulatorEvent' (..), eteEvent)
import qualified Wallet.Emulator.NodeClient as NC
import           Wallet.Emulator.Types
import qualified Wallet.Emulator.Wallet     as Wallet
import qualified Wallet.Graph

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
    let result = Eff.run $ E.runError @WalletAPIError (selectCoin inputs target)
    case result of
        Left _ ->
            Hedgehog.assert $ not $ (foldMap snd inputs) `Value.geq` target
        Right (ins, change) ->
            Hedgehog.assert $ (foldMap snd ins) == (target P.+ change)

-- | Submits a transaction that is valid in the future, then adds a number of
--   slots, then verifies that the transaction has been validated.
validFromTransaction :: Eff.Eff EmulatorEffs ()
validFromTransaction = do
    let [w1, w2] = [wallet1, wallet2]
        updateAll = processPending >>= walletsNotifyBlock [w1, w2]
        five = Ada.lovelaceValueOf 5
    updateAll

    -- Set the validation interval to (5, 5] for the
    -- transaction generated by payToPublicKey_
    -- so that the transaction can be validated only during slot 5
    let range = W.singleton 5

    walletAction w1 $ payToPublicKey_ range five pubKey2

    -- Add some blocks so that the transaction is validated
    addBlocks 50 >>= traverse_ (walletsNotifyBlock [w1, w2])
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, initialBalance P.- five),
        (w2, initialBalance P.+ five)]

txnIndex :: Property
txnIndex = property $ do
    (m, txn) <- forAll genChainTxn
    let (result, st) = Gen.runTrace m $ processPending >> simpleTrace txn
        ncState      = _chainState st
    Hedgehog.assert (Index.initialise (Chain._chainNewestFirst ncState) == Chain._index ncState)

txnIndexValid :: Property
txnIndexValid = property $ do
    (m, txn) <- forAll genChainTxn
    let (result, st) = Gen.runTrace m processPending
        idx = st ^. chainState . Chain.index
    Hedgehog.assert (isRight (Index.runValidation (Index.validateTransaction 0 txn) idx))


-- | Submit a transaction to the blockchain and assert that it has been
--   validated
simpleTrace :: Tx -> Eff.Eff EmulatorEffs ()
simpleTrace txn = do
    txn' <- walletAction wallet1 $ signTxAndSubmit txn
    block <- processPending
    assertIsValidated txn'

txnUpdateUtxo :: Property
txnUpdateUtxo = property $ do
    (Mockchain m _, txn) <- forAll genChainTxn
    let idx  = Index.initialise [m]
        slot = 1

        -- Validate a pool that contains `txn` twice. It should succeed the
        -- first and fail the second time
        Chain.ValidatedBlock [t1] [e2, e1, _] [] = Chain.validateBlock slot idx [txn, txn]
        tid = txId txn
    Hedgehog.assert (t1 == txn)
    Hedgehog.annotateShow (e1, e2)
    Hedgehog.assert $ case (e1, e2) of
        (Chain.TxnValidate i1, Chain.TxnValidationFail txi (Index.TxOutRefNotFound _)) -> i1 == tid && txi == tid
        _                                                                              -> False

validTrace :: Property
validTrace = property $ do
    (m, txn) <- forAll genChainTxn
    let (result, st) = Gen.runTrace m $ processPending >> simpleTrace txn
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == st ^. chainState . txPool)

invalidTrace :: Property
invalidTrace = property $ do
    (m, txn) <- forAll genChainTxn
    let invalidTxn = txn { txFee = mempty }
        (result, st) = Gen.runTrace m $ simpleTrace invalidTxn
    Hedgehog.assert (isLeft result)
    Hedgehog.assert ([] == st ^. chainState . txPool)
    Hedgehog.assert (not (PlutusTx.null $ _emulatorLog st))
    Hedgehog.annotateShow (_emulatorLog st)
    Hedgehog.assert (case fmap (view (logMessageContent . eteEvent)) $ reverse $ _emulatorLog st of
        ChainEvent (Chain.SlotAdd _) : ChainEvent (Chain.TxnValidationFail _ _) : _ -> True
        _                                                                           -> False)

invalidScript :: Property
invalidScript = property $ do
    (m, txn1) <- forAll genChainTxn

    -- modify one of the outputs to be a script output
    index <- forAll $ Gen.int (Range.linear 0 ((length $ txOutputs txn1) -1))
    let scriptTxn = txn1 & outputs . element index %~ \o -> scriptTxOut (txOutValue o) failValidator unitDatum
    Hedgehog.annotateShow (scriptTxn)
    let outToSpend = (txOutRefs scriptTxn) !! index
    let totalVal = Ada.fromValue $ txOutValue (fst outToSpend)

    -- try and spend the script output
    invalidTxn <- forAll $ Gen.genValidTransactionSpending (Set.fromList [scriptTxIn (snd outToSpend) failValidator unitRedeemer unitDatum]) totalVal
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
    Hedgehog.assert ([] == st ^. chainState . txPool)
    Hedgehog.assert (not (PlutusTx.null $ _emulatorLog st))
    Hedgehog.annotateShow (_emulatorLog st)
    Hedgehog.assert $ case fmap (view (logMessageContent . eteEvent)) $ reverse $ _emulatorLog st of
        ChainEvent (Chain.SlotAdd{}) : ChainEvent (Chain.TxnValidationFail _ (ScriptFailure (EvaluationError ["I always fail everything"]))) : _
            -> True
        _
            -> False

    where
        failValidator :: Validator
        failValidator = mkValidatorScript $$(PlutusTx.compile [|| wrapValidator validator ||])
        validator :: () -> () -> ValidatorCtx -> Bool
        validator _ _ _ = PlutusTx.traceError "I always fail everything"


txnFlowsTest :: Property
txnFlowsTest = property $ do
    (_, e) <- forAll $ Gen.runTraceOn Gen.generatorModel pubKeyTransactions
    let chain = e ^. chainState . Chain.chainNewestFirst
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

payToPubKeyScript2 :: Property
payToPubKeyScript2 = property $ do
    let [w1, w2, w3] = [wallet1, wallet2, wallet3]
        updateAll = processPending >>= walletsNotifyBlock [w1, w2, w3]
        payment1 = initialBalance P.- Ada.lovelaceValueOf 1
        payment2 = initialBalance P.+ Ada.lovelaceValueOf 1
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
            walletAction wallet1 $ payToPublicKey_ W.always (Ada.lovelaceValueOf 2) pubKey2
            updateAll
            traverse_ (uncurry assertOwnFundsEq) [
                (w1, initialBalance),
                (w2, initialBalance),
                (w3, initialBalance)]
    Hedgehog.assert $ isRight e

pubKeyTransactions :: Eff.Eff EmulatorEffs ()
pubKeyTransactions = do
    let [w1, w2, w3] = [wallet1, wallet2, wallet3]
        updateAll = processPending >>= walletsNotifyBlock [w1, w2, w3]
        five = Ada.lovelaceValueOf 5
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

genChainTxn :: Hedgehog.MonadGen m => m (Mockchain, Tx)
genChainTxn = do
    m <- Gen.genMockchain
    txn <- Gen.genValidTransaction m
    pure (m, txn)

initialBalance :: Value
initialBalance = Ada.lovelaceValueOf 100000
