{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
module Spec.Game(tests) where

import qualified Language.Plutus.Contract.Prompt.Event         as Event
import           Language.Plutus.Contract.Test
import qualified Language.PlutusTx                             as PlutusTx
import           Language.PlutusTx.Coordination.Contracts.Game (LockParams (..), game, gameAddress,
                                                                gameValidator, guessTrace, guessWrongTrace, lockTrace,
                                                                validateGuess)
import qualified Ledger.Value                                  as Value
import qualified Spec.Lib                                      as Lib
import           Spec.Lib                                      (timesFeeAdjust)
import           Test.Tasty
import qualified Test.Tasty.HUnit                              as HUnit

w1, w2 :: Wallet
w1 = Wallet 1
w2 = Wallet 2

tests :: TestTree
tests = testGroup "game"
    [ checkPredicate "Expose 'lock' endpoint and watch game address"
        game
        (endpointAvailable w1 "lock" <> interestingAddress w1 gameAddress)
        $ pure ()

    , checkPredicate "'lock' endpoint submits a transaction"
        game
        (anyTx w1)
        $ addEvent w1 (Event.endpointJson "lock" (LockParams "secret" 10))

    , checkPredicate "'guess' endpoint is available after locking funds"
        game
        (endpointAvailable w2 "guess")
        lockTrace

    , checkPredicate "guess right (unlock funds)"
        game
        (walletFundsChange w2 (1 `timesFeeAdjust` 10)
            <> walletFundsChange w1 (1 `timesFeeAdjust` (-10)))
        guessTrace

    , checkPredicate "guess wrong"
        game
        (walletFundsChange w2 Value.zero
            <> walletFundsChange w1 (1 `timesFeeAdjust` (-10)))
        guessWrongTrace
    , Lib.goldenPir "test/Spec/game.pir" $$(PlutusTx.compile [|| validateGuess ||])
    , HUnit.testCase "script size is reasonable" (Lib.reasonable gameValidator 25000)
    ]
