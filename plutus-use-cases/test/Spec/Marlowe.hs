{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-unused-do-bind #-}
module Spec.Marlowe(tests) where

import           Data.Either                                         (isRight)
import           Control.Monad                                        (void)
import qualified Data.Map                                            as Map
import           Hedgehog                                            (Property, forAll, property)
import qualified Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog                                 (testProperty, HedgehogTestLimit(..))

import Ledger hiding (Value)
import qualified Ledger
import Ledger.Validation (OracleValue(..), Signed(..))
import qualified Ledger.Validation                                as Validation
import           Wallet                                           (PubKey (..))
import           Wallet.Emulator
import qualified Wallet.Generators                                as Gen
import qualified Language.PlutusTx
import           Language.Marlowe.Compiler
import Language.Marlowe.Escrow                            as Escrow

newtype MarloweScenario = MarloweScenario { mlInitialBalances :: Map.Map PubKey Ledger.Value }

tests :: TestTree
tests = localOption (HedgehogTestLimit $ Just 3) $ testGroup "Marlowe" [
        testProperty "Oracle Commit/Pay works" oraclePayment,
        testProperty "Escrow Contract" escrowTest,
        -- testProperty "invalid contract: duplicate IdentCC" duplicateIdentCC,
        testProperty "can't commit after timeout" cantCommitAfterStartTimeout,
        testProperty "redeem after commit expired" redeemAfterCommitExpired
        ]

-- | Run a trace with the given scenario and check that the emulator finished
--   successfully with an empty transaction pool.
checkMarloweTrace :: MarloweScenario -> Trace MockWallet () -> Property
checkMarloweTrace MarloweScenario{mlInitialBalances} t = property $ do
    let model = Gen.generatorModel { Gen.gmInitialBalance = mlInitialBalances }
    (result, st) <- forAll $ Gen.runTraceOn model t
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == _txPool st)


updateAll :: [Wallet] -> Trace MockWallet ()
updateAll wallets = processPending >>= void . walletsNotifyBlock wallets

getScriptOutFromTx :: Tx -> (TxOut', TxOutRef')
getScriptOutFromTx tx = head . filter (isPayToScriptOut . fst) . txOutRefs $ tx

perform :: Wallet -> m () -> Trace m (TxOut', TxOutRef')
perform actor action = do
    [tx] <- walletAction actor action
    processPending >>= void . walletsNotifyBlock [actor]
    assertIsValidated tx
    return $ getScriptOutFromTx tx

withContract
    :: [Wallet]
    -> Contract
    -> ((TxOut', TxOutRef') -> Trace MockWallet (TxOut', TxOutRef'))
    -> Trace MockWallet ()
withContract wallets contract f = do
    [tx] <- walletAction creator (createContract contract 12)
    let txOut = getScriptOutFromTx tx
    update
    assertIsValidated tx

    tx1Out <- f txOut

    [tx] <- walletAction creator (endContract tx1Out)
    update
    assertIsValidated tx
  where
    creator = head wallets
    update  = updateAll wallets

oraclePayment :: Property
oraclePayment = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, 1000), (PubKey 2, 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        bob = Wallet 2
        oracle = PubKey 42
        update = updateAll [alice, bob]
    update

    let contract = CommitCash (IdentCC 1) (PubKey 2) (ValueFromOracle oracle (Value 0)) 128 256
            (Pay (IdentPay 1) (PubKey 2) (PubKey 1) (Committed (IdentCC 1)) 256 Null)
            Null

    let oracleValue = OracleValue (Signed (oracle, (Validation.Height 2, 100)))

    withContract [alice, bob] contract $ \txOut -> do
        txOut <- bob `perform` commit
            txOut
            [oracleValue] []
            (IdentCC 1)
            100
            (State [(IdentCC 1, (PubKey 2, NotRedeemed 100 256))] [])
            (Pay (IdentPay 1) (PubKey 2) (PubKey 1) (Committed (IdentCC 1)) 256 Null)

        alice `perform` receivePayment txOut
            [] []
            (IdentPay 1)
            100
            (State [] [])
            Null

    assertOwnFundsEq alice 1100
    assertOwnFundsEq bob 677
    return ()

cantCommitAfterStartTimeout :: Property
cantCommitAfterStartTimeout = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, 1000), (PubKey 2, 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        bob = Wallet 2
        update = updateAll [alice, bob]
    update

    let contract = CommitCash (IdentCC 1) (PubKey 2) (Value 100) 128 256 Null Null

    withContract [alice, bob] contract $ \txOut -> do

        addBlocks 200

        walletAction bob $ commit
            txOut
            [] []
            (IdentCC 1)
            100
            (State [(IdentCC 1, (PubKey 2, NotRedeemed 100 256))] [])
            Null
        update
        return txOut

    assertOwnFundsEq alice 1000
    assertOwnFundsEq bob 777
    return ()

duplicateIdentCC :: Property
duplicateIdentCC = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, 1000), (PubKey 2, 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        bob = Wallet 2
        update = updateAll [alice, bob]
    update

    let contract = CommitCash (IdentCC 1) (PubKey 1) (Value 100) 128 256
            (CommitCash (IdentCC 1) (PubKey 1) (Value 100) 128 256 Null Null)
            Null

    withContract [alice, bob] contract $ \txOut -> return txOut

    assertOwnFundsEq alice 1000
    assertOwnFundsEq bob 777
    return ()

redeemAfterCommitExpired :: Property
redeemAfterCommitExpired = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, 1000), (PubKey 2, 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        bob = Wallet 2
        update = updateAll [alice, bob]
        identCC = (IdentCC 1)
    update
    let contract = CommitCash identCC (PubKey 2) (Value 100) 128 256 Null Null
    withContract [alice, bob] contract $ \txOut -> do

        txOut <- bob `perform` commit
            txOut
            [] []
            (IdentCC 1)
            100
            (State [(identCC, (PubKey 2, NotRedeemed 100 256))] [])
            Null

        addBlocks 300

        bob `perform` redeem txOut [] [] identCC 100 (State [] []) Null

    assertOwnFundsEq alice 1000
    assertOwnFundsEq bob 777
    return ()

escrowTest :: Property
escrowTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, 1000), (PubKey 2, 777), (PubKey 3, 555)  ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        alicePk = PubKey 1
        bob = Wallet 2
        bobPk = PubKey 2
        carol = Wallet 3
        carolPk = PubKey 3
        update = updateAll [alice, bob, carol]
    update

    let contract = Escrow.escrowContract

    withContract [alice, bob, carol] contract $ \txOut -> do
        txOut <- alice `perform` commit
            txOut
            [] []
            (IdentCC 1)
            450
            (State [(IdentCC 1, (PubKey 1, NotRedeemed 450 100))] [])
            (When (OrObs (two_chose alicePk bobPk carolPk 0)
                                 (two_chose alicePk bobPk carolPk 1))
                          90
                          (Choice (two_chose alicePk bobPk carolPk 1)
                                  (Pay iP1 alicePk bobPk
                                       (Committed iCC1)
                                       100
                                       Null)
                                  redeem_original)
                          redeem_original)

        addBlocks 50

        let choices = [((IdentChoice 1, alicePk), 1), ((IdentChoice 2, bobPk), 1), ((IdentChoice 3, carolPk), 1)]
        bob `perform` receivePayment txOut
            []
            choices
            (IdentPay 1)
            450
            (State [] choices)
            Null

    assertOwnFundsEq alice 550
    assertOwnFundsEq bob 1227
    assertOwnFundsEq carol 555
    return ()
