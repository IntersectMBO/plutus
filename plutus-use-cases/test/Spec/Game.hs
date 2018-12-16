module Spec.Game(tests) where

import           Control.Monad                                 (void)
import           Data.Either                                   (isRight)
import           Data.Foldable                                 (traverse_)
import qualified Data.Map                                      as Map

import           Hedgehog                                      (Property, forAll, property)
import qualified Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog                           (testProperty)

import qualified Ledger
import           Wallet.API                                    (PubKey (..))
import           Wallet.Emulator
import qualified Wallet.Generators                             as Gen

import           Language.PlutusTx.Coordination.Contracts.Game (guess, lock, startGame)

tests :: TestTree
tests = testGroup "game" [
    testProperty "lock" lockProp,
    testProperty "guess right" guessRightProp,
    testProperty "guess wrong" guessWrongProp
    ]

lockProp :: Property
lockProp = checkTrace $ do
    lockFunds
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, startingBalance - 10),
        (w2, startingBalance)]

guessRightProp :: Property
guessRightProp = checkTrace $ do
    void $ walletAction w2 startGame
    lockFunds
    void $ walletAction w2 (guess "abcde")
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, startingBalance - 10),
        (w2, startingBalance + 10)]

guessWrongProp :: Property
guessWrongProp = checkTrace $ do
    void $ walletAction w2 startGame
    lockFunds
    void $ walletAction w2 (guess "a")
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, startingBalance - 10),
        (w2, startingBalance)]

-- | Funds available to wallets at the beginning.
startingBalance :: Ledger.Value
startingBalance = 1000000

-- | Wallet 1
w1 :: Wallet
w1 = Wallet 1

-- | Wallet 2
w2 :: Wallet
w2 = Wallet 2

lockFunds :: Trace MockWallet ()
lockFunds = void $ walletAction w1 (lock "abcde" 10) >> updateAll

checkTrace :: Trace MockWallet () -> Property
checkTrace t = property $ do
    let
        ib = Map.fromList [
            (PubKey 1, startingBalance),
            (PubKey 2, startingBalance)]
        model = Gen.generatorModel { Gen.gmInitialBalance = ib }
    (result, st) <- forAll $ Gen.runTraceOn model (updateAll >> t)
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == _txPool st)

-- | Validate all pending transactions and notify all wallets
updateAll :: Trace MockWallet ()
updateAll =
    processPending >>= void . walletsNotifyBlock [w1, w2]
