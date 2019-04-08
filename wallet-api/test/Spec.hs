{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
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
import qualified Ledger.Map
import           Data.Monoid                (Sum (..))
import qualified Data.Set                   as Set
import           Data.String                (IsString(fromString))
import           Hedgehog                   (Property, forAll, property)
import qualified Hedgehog
import qualified Hedgehog.Gen               as Gen
import qualified Hedgehog.Range             as Range
import qualified Language.PlutusTx.Builtins as Builtins
import qualified Language.PlutusTx.Prelude  as PlutusTx
import           Test.Tasty
import           Test.Tasty.Hedgehog        (testProperty)
import qualified Test.Tasty.HUnit as HUnit
import           Test.Tasty.HUnit (testCase)
import           LedgerBytes                as LedgerBytes
import           Ledger
import qualified Ledger.Ada                 as Ada
import qualified Ledger.Index               as Index
import qualified Ledger.Value               as Value
import           Ledger.Value.TH            (CurrencySymbol,Value(Value))
import           Wallet
import qualified Wallet.API                 as W
import           Wallet.Emulator
import           Wallet.Generators          (Mockchain (..))
import qualified Wallet.Generators          as Gen
import qualified Wallet.Graph

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "all tests" [
    testGroup "UTXO model" [
        testProperty "initial transaction is valid" initialTxnValid,
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
    testGroup "intervals" [
        testProperty "member" intvlMember,
        testProperty "contains" intvlContains
        ],
    testGroup "values" [
        testProperty "additive identity" valueAddIdentity,
        testProperty "additive inverse" valueAddInverse,
        testProperty "scalar identity" valueScalarIdentity,
        testProperty "scalar distributivity" valueScalarDistrib
        ],
    testGroup "Etc." [
        testProperty "splitVal" splitVal,
        testProperty "selectCoin" selectCoinProp,
        testProperty "txnFlows" txnFlowsTest,
        testProperty "encodeByteString" encodeByteStringTest,
        testProperty "encodeSerialise" encodeSerialiseTest
        ],
    testGroup "LedgerBytes" [
        testProperty "show-fromHex" ledgerBytesShowFromHexProp,
        testProperty "toJSON-fromJSON" ledgerBytesToJSONProp
        ],
    testGroup
      "CurrencySymbol"
      (let jsonString :: BSL.ByteString
           jsonString = "{\"getValue\":[[{\"unCurrencySymbol\":\"0\"},50]]}"
           value = Value (Ledger.Map.singleton (Value.currencySymbol "0") 50)
        in [ testCase "decoding" $
             HUnit.assertEqual "Simple Decode" (Right value) (JSON.eitherDecode jsonString)
           , testCase "encoding" $ HUnit.assertEqual "Simple Encode" jsonString (JSON.encode value)
           ])
    ]

wallet1, wallet2, wallet3 :: Wallet
wallet1 = Wallet 1
wallet2 = Wallet 2
wallet3 = Wallet 3

pubKey1, pubKey2, pubKey3 :: PubKey
pubKey1 = walletPubKey wallet1
pubKey2 = walletPubKey wallet2
pubKey3 = walletPubKey wallet3

initialTxnValid :: Property
initialTxnValid = property $ do
    (i, _) <- forAll . pure $ Gen.genInitialTransaction Gen.generatorModel
    Gen.assertValid i Gen.emptyChain

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
        failValidator = ValidatorScript $ $$(compileScript [|| \() () () -> $$(PlutusTx.traceH) "I always fail everything" (Builtins.error @()) ||])

splitVal :: Property
splitVal = property $ do
    i <- forAll $ Gen.int $ Range.linear 1 (100000 :: Int)
    n <- forAll $ Gen.int $ Range.linear 1 100
    vs <- forAll $ Gen.splitVal n i
    Hedgehog.assert $ sum vs == i
    Hedgehog.assert $ length vs <= n

valueAddIdentity :: Property
valueAddIdentity = property $ do
    vl1 <- forAll Gen.genValue
    Hedgehog.assert $ Value.eq vl1 (vl1 `Value.plus` Value.zero)
    Hedgehog.assert $ Value.eq vl1 (Value.zero `Value.plus` vl1)

valueAddInverse :: Property
valueAddInverse = property $ do
    vl1 <- forAll Gen.genValue
    let vl1' = Value.negate vl1
    Hedgehog.assert $ Value.eq Value.zero (vl1 `Value.plus` vl1')

valueScalarIdentity :: Property
valueScalarIdentity = property $ do
    vl1 <- forAll Gen.genValue
    Hedgehog.assert $ Value.eq vl1 (Value.scale 1 vl1)

valueScalarDistrib :: Property
valueScalarDistrib = property $ do
    vl1 <- forAll Gen.genValue
    vl2 <- forAll Gen.genValue
    scalar <- forAll (Gen.int Range.linearBounded)
    let r1 = Value.scale scalar (Value.plus vl1 vl2)
        r2 = Value.plus (Value.scale scalar vl1) (Value.scale scalar vl2)
    Hedgehog.assert $ Value.eq r1 r2

selectCoinProp :: Property
selectCoinProp = property $ do
    inputs <- forAll $ zip [1..] <$> Gen.list (Range.linear 1 1000) Gen.genValueNonNegative
    target <- forAll Gen.genValueNonNegative
    let result = runExcept (selectCoin inputs target)
    case result of
        Left _ ->
            Hedgehog.assert $ (fold $ snd <$> inputs) `Value.lt` target
        Right (ins, change) ->
            Hedgehog.assert $ (fold $ snd <$> ins) `Value.eq` (target `Value.plus` change)

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
                t2 = fundsAtAddressT (pubKeyAddress pkTarget) (W.intervalFrom (Ada.adaValueOf 1))
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

intvlMember :: Property
intvlMember = property $ do
    (i1, i2) <- forAll $ (,) <$> Gen.int Range.linearBounded <*> Gen.int Range.linearBounded
    let (from, to) = (Slot $ min i1 i2, Slot $ max i1 i2)
        i          = W.interval from to
    Hedgehog.assert $ W.member from i || W.empty i
    Hedgehog.assert $ (not $ W.member to i) || W.empty i

intvlContains :: Property
intvlContains = property $ do
    -- generate two intervals from a sorted list of ints
    -- the outer interval contains the inner interval
    ints <- forAll $ traverse (const $ Gen.int Range.linearBounded) [1..4]
    let [i1, i2, i3, i4] = fmap Slot $ sort ints
        outer = W.interval i1 i4
        inner = W.interval i2 i3

    Hedgehog.assert $ W.contains outer inner

encodeByteStringTest :: Property
encodeByteStringTest = property $ do
    bs <- forAll $ Gen.bytes $ Range.linear 0 1000
    let enc    = JSON.String $ JSON.encodeByteString bs
        result = Aeson.iparse JSON.decodeByteString enc

    Hedgehog.assert $ result == Aeson.ISuccess bs

encodeSerialiseTest :: Property
encodeSerialiseTest = property $ do
    txt <- forAll $ Gen.text (Range.linear 0 1000) Gen.unicode
    let enc    = JSON.String $ JSON.encodeSerialise txt
        result = Aeson.iparse JSON.decodeSerialise enc

    Hedgehog.assert $ result == Aeson.ISuccess txt

ledgerBytesShowFromHexProp :: Property
ledgerBytesShowFromHexProp = property $ do
    bts <- forAll $ LedgerBytes <$> Gen.genSizedByteString
    let result = LedgerBytes.fromHex $ fromString $ show bts
    
    Hedgehog.assert $ result == bts

ledgerBytesToJSONProp :: Property
ledgerBytesToJSONProp = property $ do
    bts <- forAll $ LedgerBytes <$> Gen.genSizedByteString
    let enc    = JSON.toJSON bts
        result = Aeson.iparse JSON.parseJSON enc

    Hedgehog.assert $ result == Aeson.ISuccess bts
