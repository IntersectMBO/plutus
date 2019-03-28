{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Main(main) where

import           Control.Lens                             hiding (elements, from, index, to, transform)
import           Control.Monad.Except                     (runExcept)
import           Control.Monad.State

import qualified Data.Aeson                               as JSON
import qualified Data.Aeson.Extras                        as JSON
import qualified Data.Aeson.Internal                      as Aeson
import qualified Data.ByteString                          as BSS
import           Data.Either
import           Data.Foldable                            (fold, traverse_)
import           Data.List
import qualified Data.Map                                 as Map
import           Data.Maybe
import qualified Data.Set                                 as Set

import           Ledger                                   hiding (inputs)
import qualified Ledger.Ada                               as Ada
import qualified Ledger.Index                             as Index
import qualified Ledger.Value                             as Value

import qualified Hedgehog
import qualified Hedgehog.Gen                             as Gen
import qualified Hedgehog.Range                           as Range
import           Test.QuickCheck
import           Test.StateMachine                        hiding (elem)
import           Test.Tasty
import qualified Test.Tasty.Hedgehog                      as Hedgehog
import           Test.Tasty.QuickCheck

import qualified Language.PlutusTx.Builtins               as Builtins
import qualified Language.PlutusTx.Prelude                as PlutusTx

import qualified Wallet.API                               as W
import           Wallet.Emulator                          as Emulator
import           Wallet.Generators.Mockchain
import qualified Wallet.Generators.Mockchain              as Mockchain
import           Wallet.Generators.Mockchain.StateMachine

import qualified Wallet.Graph

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "all tests"
        [ testGroup "UTxO model"
          [ testProperty "initial transaction is valid" initialTxnValid
          , testProperty "validate transaction" txnValid
          , testProperty "validate transaction when it can be validated" txnValidRange
          , testProperty "update UTxO set after each transaction" txnUpdateUtxo
          , testProperty "invalid transactions can't be validated" txnInvalid
          , testProperty "mockchain slot is synchronized with emulator slot" slotCorrect
          , testProperty "total blockchain value is conserved" valueConserved
          , testProperty "outputs are spent at most once" outputsConserved
          ]
        , testGroup "UTxO index"
          [ testProperty "recreate the utxo index of a blockchain" chainIndex
          , testProperty "use the index to validate transactions" txnIndexValid
          ]
        , testGroup "traces"
          [ testProperty "accept valid txn" validTrace
          ,testProperty "reject invalid txn" invalidTrace
          ,testProperty "notify wallet" notifyWallet
          ,testProperty "react to blockchain events" eventTrace
          ,testProperty "watch funds at an address" notifyWallet
          ,testProperty "log script validation failures" invalidScript
          ,testProperty "payToPubkey" payToPubKeyScript
          ,testProperty "payToPubkey-2" payToPubKeyScript2
          ]
        , testGroup "intervals"
          [ testProperty "member" intvlMember
          , testProperty "contains" intvlContains
        ]
        , testGroup "values"
          [ testProperty "additive identity" valueAddIdentity
          , testProperty "additive inverse" valueAddInverse
          , testProperty "scalar identity" valueScalarIdentity
          , testProperty "scalar distributivity" valueScalarDistrib
          ]
        , testGroup "Etc."
          [ testProperty "splitVal" splitValProp
          , testProperty "selectCoin" selectCoinProp
          , testProperty "txnFlows" txnFlowsTest
          , Hedgehog.testProperty "encodeByteString" encodeByteStringTest
          , Hedgehog.testProperty "encodeSerialise" encodeSerialiseTest
          ]
        ]

keys :: [PubKey]
keys = Set.toList $ defaultModel ()^.chainKeys

-- A key that will never submit transactions automatically, useful for testing purposes
testKey :: PubKey
testKey = head keys

gm :: a -> GeneratorModel a
gm a = defaultModel a & transactionKeys .~ Set.fromList (tail keys)

discardUnless :: Bool -> Property
discardUnless True  = property True
discardUnless False = label "Discarded" $ property Discard

-- UTxO model

initialTxnValid :: Property
initialTxnValid = property $ do
    ib <- zip (PubKey <$> [1 ..]) <$> (flip vectorOf Mockchain.genValueNonNegative =<< choose (1, 50))
    pure $ Main.isValid emptyEmulatorState (fst $ initialTransaction ib)

txnValid :: Property
txnValid = forAllChains gm' $ \_ checked -> discardUnless checked
    where gm' = gm False & userActions .~ [generateAndVerifyValidTransaction]
          generateAndVerifyValidTransaction mc = do
              tx <- genValidTransaction keys keys mc (gm'^.feeEstimator)
              pure $ checkAndRemember "Generate a valid transaction" $ \es ->
                  (Annotate "Check that the transaction is valid according to the emulator"
                  $ Boolean
                  $ Main.isValid es tx) :&&
                  (Annotate "Check that the transaction is valid according to the Mockchain"
                  $ Boolean
                  $ Mockchain.isValid (mc^.currentSlot) (mc^.utxo) tx)

txnValidRange :: Property
txnValidRange = forAllChains gm' $ \_ tx -> discardUnless $ isJust tx
    where gm' = gm Nothing
                   & userActions .~ [generateValidTransaction]
                   & userInvariant ?~ checkTransaction
          generateValidTransaction mc = do
              let now = getSlot $ mc^.currentSlot
              start <- choose (now, now + 10)
              duration <- choose (1, 10)
              let range = W.interval (Slot start) (Slot $ start + duration)
              w <- elements $ wallets gm'
              tx <- set validRange range <$> genSafeTransaction [testKey] keys mc (gm'^.feeEstimator)
              pure $ Action { uaLabel = "Generate a valid transaction"
                            , uaCommands = [Transaction w tx]
                            , uaConcrete = const $ Just (Slot start, tx)
                            , uaPostcondition = \_ _-> Top
                            }
          checkTransaction _ Nothing = Top
          checkTransaction es (Just (start, tx))
              | now < start = Annotate "Transaction can't be validated early"
                              (Not $ Boolean $ Main.isValid es tx) :&& (Not $ Boolean $ tx `elem` chain)
              | now == start = Annotate "Transaction can be validated" (Boolean $ Main.isValid es tx)
              | now >= start + 1 = Annotate "Transaction has been validated" (Boolean $ tx `elem` chain)
              | otherwise = Top
              where now   = lastSlot (es^.chainNewestFirst)
                    chain = concat (es^.chainNewestFirst)

txnUpdateUtxo :: Property
txnUpdateUtxo = forAllChains (gm ()) $ \es () -> property $
    length (es^.txPool) >= 1 ==> do
        tx <- elements $ es^.txPool
        let slot = lastSlot (es^.chainNewestFirst)
            ValidatedBlock validTxns events [] _ = validateBlock slot (es^.index) (tx : es^.txPool)
            noDuplicates = nub validTxns === validTxns
            duplicatedTransactionFails = not $ null $ flip filter events $
                \case TxnValidationFail txi _
                          | txi == hashTx tx -> True
                          | otherwise -> False
                      _ -> False
        pure $ noDuplicates .&&. duplicatedTransactionFails

txnInvalid :: Property
txnInvalid = forAllChains gm' $ \_ checked -> discardUnless checked
    where gm' = gm True & userActions .~ [generateAndVerifyValidTransaction]
          generateAndVerifyValidTransaction mc = do
              tx <- genInvalidTransaction keys keys mc (gm'^.feeEstimator)
              pure $ checkAndRemember "Generate an invalid transaction" $ \es ->
                  (Annotate "Check that the transaction is invalid according to the emulator"
                   $ Not $ Boolean $ Main.isValid es tx) :&&
                  (Annotate "Check that the transaction is invalid according to the Mockchain"
                   $ Not $ Boolean $ Mockchain.isValid (mc^.currentSlot) (mc^.utxo) tx)

slotCorrect :: Property
slotCorrect = forAllChains gm' $ \_ checked -> discardUnless checked
    where gm' = gm False & userActions .~ [checkSlot]
          checkSlot mc = pure $ checkAndRemember "Mockchain slot is identical to emulator slot" $ \es ->
              Boolean (lastSlot (es^.chainNewestFirst) == mc^.currentSlot)

valueConserved :: Property
valueConserved = property $ do
    fee <- choose (0, 10)
    let gm' = gm () & feeEstimator .~ constantFee (Ada.fromInt fee)
    pure $ forAllChains gm' $ \es () ->
        let totalFunds outs   = foldl' Value.plus Value.zero $ txOutValue <$> outs
            fees              = Ada.adaValueOf $ sum $ Ada.toInt . txFee <$> join (es^.chainNewestFirst)
            totalInitialFunds = foldl' Value.plus Value.zero (snd <$> gm'^.initialBalances)
        in property $ totalFunds (getIndex $ es^.index) `Value.plus` fees === totalInitialFunds

outputsConserved :: Property
outputsConserved = property $ forAllChains (gm ()) $ \es () ->
    -- Check that every output is either spent or is part of the UTxO set
    let chain   = join $ es^.chainNewestFirst
        outs    = fold $ Set.fromList . map snd . txOutRefs <$> chain
        ins     = fold $ Set.map txInRef . txInputs <$> chain
        unspent = Set.fromList $ map fst $ Map.toList $ getIndex $ es^.index
    in property $ outs === ins `Set.union` unspent

-- UTxO index

chainIndex :: Property
chainIndex = forAllChains (gm ()) $ \es () ->
    foldr Ledger.updateUtxo Map.empty (join $ es^.chainNewestFirst) === getIndex (es^.index)

txnIndexValid :: Property
txnIndexValid = forAllChains gm' $ \_ checked -> discardUnless checked
    where gm' = gm False & userActions .~ [generateValidTransaction]
          generateValidTransaction mc = do
              txn <- genValidTransaction keys keys mc (gm'^.feeEstimator)
              pure $ checkAndRemember "Generate a valid transaction" $ \es ->
                  Annotate "Check that the index can validate the transaction"
                  $ Boolean
                  $ isRight (Index.runValidation (Index.validateTransaction 0 txn) (es^.index))

-- traces

initialState :: EmulatorState
initialState = emulatorState' [fst $ initialTransaction $ gm()^.initialBalances]

initialBalance :: Value.Value
initialBalance = Ada.adaValueOf 100000

validTrace :: Property
validTrace = forAllChains (gm ()) $ \es () -> property $ do
    let mc = Mockchain.fromEmulatorState es
    txn <- genSafeTransaction keys keys mc (gm()^.feeEstimator)
    let (result, st) = runTraceState es $ processPending >> simpleTrace txn
    pure $ isRight result .&&. [] == _txPool st

invalidTrace :: Property
invalidTrace = forAllChains (gm ()) $ \es () -> property $ do
    let mc = Mockchain.fromEmulatorState es
    txn <- genInvalidTransaction keys keys mc (gm()^.feeEstimator)
    let (result, es') = runTraceState es $ processPending >> simpleTrace txn
    pure $
        isLeft result
        .&&. [] == _txPool es'
        .&&. not (null $ _emulatorLog es')
        .&&. case _emulatorLog es' of
                 SlotAdd _ : TxnValidationFail _ _ : _ -> True
                 _                                     -> False

invalidScript :: Property
invalidScript = forAllChains (gm ()) $ \es () -> property $ do
    let mc = Mockchain.fromEmulatorState es
    txn1 <- genSafeTransaction keys keys mc (gm()^.feeEstimator)

    -- modify one of the outputs to be a script output
    i <- choose (0, (length $ txOutputs txn1) -1)
        `suchThat` ((Value.zero /=) . txOutValue . fst . ((txOutRefs txn1) !!))
    let scriptTxn = txn1 & outputs . element i %~ \o -> scriptTxOut (txOutValue o) failValidator unitData
    let outToSpend = (txOutRefs scriptTxn) !! i
    let totalVal = Ada.fromValue $ txOutValue (fst outToSpend)

    -- try and spend the script output
    invalidTxn <- genTransactionSpending' [PubKey 1]
                                          (Set.fromList [scriptTxIn (snd outToSpend) failValidator unitRedeemer])
                                          totalVal
                                          (gm()^.feeEstimator)
    let invalidHash = hashTx invalidTxn

    let (result, st) = runTraceState es $ do
            processPending
            walletAction (Wallet 1) $ W.submitTxn scriptTxn
            processPending
            walletAction (Wallet 1) $ W.submitTxn invalidTxn
            processPending

    pure $ counterexample (show scriptTxn)
        $ counterexample (show invalidTxn)
        $ counterexample (show invalidHash)
        $ isRight result
        .&&. [] === _txPool st
        .&&. not (null $ st^.emulatorLog)
        .&&. (counterexample (show $ st^.emulatorLog) $
              flip any (_emulatorLog st) $ \case
                     TxnValidationFail txn (ScriptFailure ["I always fail everything"]) -> txn == invalidHash
                     _ -> False)

    where
        failValidator :: ValidatorScript
        failValidator = ValidatorScript $$(compileScript [|| \() () () -> $$(PlutusTx.traceH) "I always fail everything" (Builtins.error @()) ||])

assertRight :: (Show a) => Either a b -> Property
assertRight (Right _) = property True
assertRight (Left l)  = counterexample (show l) $ property False

notifyWallet :: Property
notifyWallet = assertRight $ fst $ runTraceState initialState $ do
    let w = Wallet 1
    processPending >>= walletNotifyBlock w
    assertOwnFundsEq w initialBalance

eventTrace :: Property
eventTrace = assertRight $ fst $ runTraceState initialState $ do
    let w = Wallet 1
    processPending >>= walletNotifyBlock w
    let mkPayment =
            W.EventHandler $ \_ -> W.payToPublicKey_ W.always (Ada.adaValueOf 100) (PubKey 2)
        trigger = W.slotRangeT (W.intervalFrom 3)

    -- schedule the `mkPayment` action to run when slot 3 is
    -- reached.
    b1 <- walletAction (Wallet 1) $ W.register trigger mkPayment
    walletNotifyBlock w b1

    -- advance the clock to trigger `mkPayment`
    addBlocks 2 >>= traverse_ (walletNotifyBlock w)
    void (processPending >>= walletNotifyBlock w)
    assertOwnFundsEq w (initialBalance `Value.minus` Ada.adaValueOf 100)

payToPubKeyScript :: Property
payToPubKeyScript = property $ assertRight $ fst $ runTraceState initialState pubKeyTransactions

payToPubKeyScript2 :: Property
payToPubKeyScript2 = property $ assertRight $ fst $ runTraceState initialState $ do
    let [w1, w2, w3] = Wallet <$> [1, 2, 3]
        updateAll = processPending >>= walletsNotifyBlock [w1, w2, w3]
        payment1 = initialBalance `Value.minus` Ada.adaValueOf 1
        payment2 = initialBalance `Value.plus` Ada.adaValueOf 1
    updateAll
    walletAction (Wallet 1) $ W.payToPublicKey_ W.always payment1 (PubKey 2)
    updateAll
    walletAction (Wallet 2) $ W.payToPublicKey_ W.always payment2 (PubKey 3)
    updateAll
    walletAction (Wallet 3) $ W.payToPublicKey_ W.always payment2 (PubKey 1)
    updateAll
    walletAction (Wallet 1) $ W.payToPublicKey_ W.always (Ada.adaValueOf 2) (PubKey 2)
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, initialBalance),
        (w2, initialBalance),
        (w3, initialBalance)]

pubKeyTransactions :: Trace MockWallet ()
pubKeyTransactions = do
    let [w1, w2, w3] = Wallet <$> [1, 2, 3]
        updateAll = processPending >>= walletsNotifyBlock [w1, w2, w3]
        five = Ada.adaValueOf 5
    updateAll
    walletAction (Wallet 1) $ W.payToPublicKey_ W.always five (PubKey 2)
    updateAll
    walletAction (Wallet 2) $ W.payToPublicKey_ W.always five (PubKey 3)
    updateAll
    walletAction (Wallet 3) $ W.payToPublicKey_ W.always five (PubKey 1)
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, initialBalance),
        (w2, initialBalance),
        (w3, initialBalance)]

watchFundsAtAddress :: Property
watchFundsAtAddress = property $ isRight $ fst $ runTraceState initialState $ do
    let w = Wallet 1
        pkTarget = PubKey 2
        mkPayment =
            W.EventHandler $ \_ -> W.payToPublicKey_ W.always (Ada.adaValueOf 100) (PubKey 2)
        t1 = W.slotRangeT (W.interval 3 4)
        t2 = W.fundsAtAddressT (pubKeyAddress pkTarget) (W.intervalFrom (Ada.adaValueOf 1))
    processPending >>= walletNotifyBlock w
    walletNotifyBlock w =<<
        (walletAction (Wallet 1) $ do
                W.register t1 mkPayment
                W.register t2 mkPayment)

            -- after 3 blocks, t1 should fire, triggering the first payment of 100 to PubKey 2
            -- after 4 blocks, t2 should fire, triggering the second payment of 100
    addBlocks 3 >>= traverse_ (walletNotifyBlock w)
    void (processPending >>= walletNotifyBlock w)
    assertOwnFundsEq w (initialBalance `Value.minus` Ada.adaValueOf 200)

flush :: EmulatorState -> EmulatorState
flush es = es { _txPool = [] }

validate :: EmulatorState -> Tx -> Maybe ValidationError
validate es tx = evalState (validateEm (lastSlot $ es^.chainNewestFirst) tx) (es^.index)

isValid :: EmulatorState -> Tx -> Bool
isValid es tx = isNothing $ validate es tx

checkTrace :: EmulatorState -> Trace MockWallet a -> Property
checkTrace es trace = case flush es `runTraceState` trace of
    (Left err, _) -> counterexample (show err) False
    (Right _, _)  -> property True

-- | Submit a transaction to the blockchain and assert that it has been
--   validated
simpleTrace :: Tx -> Trace MockWallet ()
simpleTrace txn = do
    [txn'] <- walletAction (Wallet 1) $ W.submitTxn txn
    _ <- processPending
    assertIsValidated txn'

-- intervals

intvlMember :: Property
intvlMember = property $ do
    (i1, i2) <- arbitrary
    let (from, to) = (Slot $ min i1 i2, Slot $ max i1 i2)
        i          = W.interval from to
    pure $ (W.member from i || W.empty i)
        && ((not $ W.member to i) || W.empty i)

intvlContains :: Property
intvlContains = property $ do
    -- generate two intervals from a sorted list of ints
    -- the outer interval contains the inner interval
    ints <- replicateM 4 arbitrary
    let [i1, i2, i3, i4] = Slot <$> sort ints
        outer = W.interval i1 i4
        inner = W.interval i2 i3
    pure $ W.contains outer inner

-- values

valueAddIdentity :: Property
valueAddIdentity = property $ do
    vl1 <- genValue
    pure $ Value.eq vl1 (vl1 `Value.plus` Value.zero)
        .&&.  Value.eq vl1 (Value.zero `Value.plus` vl1)

valueAddInverse :: Property
valueAddInverse = property $ do
    vl1 <- genValue
    let vl1' = Value.negate vl1
    pure $ Value.eq Value.zero (vl1 `Value.plus` vl1')

valueScalarIdentity :: Property
valueScalarIdentity = property $ do
    vl1 <- genValue
    pure $ Value.eq vl1 (Value.scale 1 vl1)

valueScalarDistrib :: Property
valueScalarDistrib = property $ do
    vl1 <- genValue
    vl2 <- genValue
    scalar <- arbitrary
    let r1 = Value.scale scalar (Value.plus vl1 vl2)
        r2 = Value.plus (Value.scale scalar vl1) (Value.scale scalar vl2)
    pure $ Value.eq r1 r2

-- Etc.

splitValProp :: Property
splitValProp = property $ do
    i <- choose (1, 100000)
    n <- choose (1, 100)
    vs <- Mockchain.splitVal n i
    pure $ sum vs == i && length vs <= n

selectCoinProp :: Property
selectCoinProp = property $ do
    inputs <- zip [1..] <$> (flip vectorOf Mockchain.genValueNonNegative =<< choose (1, 1000))
    target <- Mockchain.genValueNonNegative
    let result = runExcept (selectCoin inputs target)
        sumValue = foldl' Value.plus Value.zero
    pure $ case result of
        Left _ ->
            (sumValue $ snd <$> inputs) `Value.lt` target
        Right (ins, change) ->
            (sumValue $ snd <$> ins) `Value.eq` (target `Value.plus` change)

txnFlowsTest :: Property
txnFlowsTest = property $ forAllChains (gm ()) $ \es _ ->
    let chain = es^.chainNewestFirst
        numTx = length $ fold chain
        flows = Wallet.Graph.txnFlows [] chain
        -- there should be at least one link per tx
        -- plus some for the unspent outputs
    in property $ not (null flows) ==> length flows > numTx

encodeByteStringTest :: Hedgehog.Property
encodeByteStringTest = Hedgehog.property $ do
    bs <- Hedgehog.forAll $ Gen.bytes $ Range.linear 0 1000
    let enc    = JSON.String $ JSON.encodeByteString bs
        result = Aeson.iparse JSON.decodeByteString enc
    Hedgehog.assert $ result == Aeson.ISuccess bs

encodeSerialiseTest :: Hedgehog.Property
encodeSerialiseTest = Hedgehog.property $ do
    txt <- Hedgehog.forAll $ Gen.text (Range.linear 0 1000) Gen.unicode
    let enc    = JSON.String $ JSON.encodeSerialise txt
        result = Aeson.iparse JSON.decodeSerialise enc
    Hedgehog.assert $ result == Aeson.ISuccess txt
