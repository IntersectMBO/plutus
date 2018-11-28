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

import           Wallet.API                                          (PubKey (..))
import           Wallet.Emulator                                     hiding (Value)
import qualified Wallet.Generators                                   as Gen
import           Wallet.UTXO.Runtime                           (OracleValue (..), Signed (..))

import qualified Language.Plutus.Runtime                             as Runtime
import           Language.Marlowe.Compiler
import qualified Language.Marlowe.Escrow                            as Escrow
import qualified Wallet.UTXO                                         as UTXO

newtype MarloweScenario = MarloweScenario { mlInitialBalances :: Map.Map PubKey UTXO.Value }

tests :: TestTree
tests = localOption (HedgehogTestLimit $ Just 3) $ testGroup "Marlowe" [
        testProperty "Oracle Commit/Pay works" oraclePayment,
        testProperty "Escrow Contract" escrowTest,
        testProperty "invalid contract: duplicate IdentCC" duplicateIdentCC,
        testProperty "can't commit after timeout" cantCommitAfterStartTimeout,
        testProperty "redeem after commit expired" redeemAfterCommitExpired
        ]

-- | Run a trace with the given scenario and check that the emulator finished
--   successfully with an empty transaction pool.
checkMarloweTrace :: MarloweScenario -> Trace EmulatedWalletApi () -> Property
checkMarloweTrace MarloweScenario{mlInitialBalances} t = property $ do
    let model = Gen.generatorModel { Gen.gmInitialBalance = mlInitialBalances }
    (result, st) <- forAll $ Gen.runTraceOn model t
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == _txPool st)


updateAll :: [Wallet] -> Trace EmulatedWalletApi ()
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
    -> ((TxOut', TxOutRef') -> Trace EmulatedWalletApi (TxOut', TxOutRef'))
    -> Trace EmulatedWalletApi ()
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

    let oracleValue = OracleValue (Signed (oracle, (Runtime.Height 2, 100)))

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
        alicePK = PubKey 1
        bob = Wallet 2
        bobPK = PubKey 2
        carol = Wallet 3
        carolPK = PubKey 3
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
            (Pay (IdentPay 1) (PubKey 1) (PubKey 2) (Committed (IdentCC 1)) 100 Null)

        addBlocks 50

        let choices = [((IdentChoice 1, alicePK), 1), ((IdentChoice 2, bobPK), 1), ((IdentChoice 3, carolPK), 1)]
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
