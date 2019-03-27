module Spec.Game(tests) where

import           Control.Monad                                 (void)
import           Control.Monad.IO.Class
import           Data.Either                                   (isRight)
import           Data.Foldable                                 (traverse_)
import qualified Data.Map                                      as Map

import           Hedgehog                                      (Property, forAll, property)
import qualified Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog                           (testProperty)
import qualified Test.Tasty.HUnit                              as HUnit

import qualified Ledger
import qualified Ledger.Ada                                    as Ada
import qualified Ledger.Value                                  as Value
import           Wallet.Emulator
import qualified Wallet.Generators                             as Gen

import           Language.PlutusTx.Coordination.Contracts.Game (gameValidator, guess, lock, startGame)

w1, w2 :: Wallet
w1 = Gen.wallet1
w2 = Gen.wallet2

tests :: TestTree
tests = testGroup "game" [
    testProperty "lock" lockProp,
    testProperty "guess right" guessRightProp,
    testProperty "guess wrong" guessWrongProp,
    HUnit.testCase "script size is reasonable" size
    ]

size :: HUnit.Assertion
size = do
    let Ledger.ValidatorScript s = gameValidator
    let sz = Ledger.scriptSize s
    -- so the actual size is visible in the log
    liftIO $ putStrLn ("Script size: " ++ show sz)
    HUnit.assertBool "script too big" (sz <= 25000)

lockProp :: Property
lockProp = checkTrace $ do
    lockFunds
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, Value.minus startingBalance (Ada.adaValueOf 10)),
        (w2, startingBalance)]

guessRightProp :: Property
guessRightProp = checkTrace $ do
    void $ walletAction w2 startGame
    lockFunds
    void $ walletAction w2 (guess "abcde")
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, Value.minus startingBalance (Ada.adaValueOf 10)),
        (w2, Value.plus  startingBalance (Ada.adaValueOf 10))]

guessWrongProp :: Property
guessWrongProp = checkTrace $ do
    void $ walletAction w2 startGame
    lockFunds
    void $ walletAction w2 (guess "a")
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, Value.minus startingBalance (Ada.adaValueOf 10)),
        (w2, startingBalance)]

-- | Funds available to wallets at the beginning.
startingBalance :: Ledger.Value
startingBalance = Ada.adaValueOf 1000000

lockFunds :: Trace MockWallet ()
lockFunds = void $ walletAction w1 (lock "abcde" 10) >> updateAll

checkTrace :: Trace MockWallet () -> Property
checkTrace t = property $ do
    let
        ib = Map.fromList [
            (walletPubKey w1, startingBalance),
            (walletPubKey w2, startingBalance)]
        model = Gen.generatorModel { Gen.gmInitialBalance = ib }
    (result, st) <- forAll $ Gen.runTraceOn model (updateAll >> t)
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == _txPool st)

-- | Validate all pending transactions and notify all wallets
updateAll :: Trace MockWallet ()
updateAll =
    processPending >>= void . walletsNotifyBlock [w1, w2]
