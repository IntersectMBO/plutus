{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}

module Spec.Game
    ( tests
    ) where

import           Language.Plutus.Contract                      (ContractError)
import           Language.Plutus.Contract.Test
import qualified Language.PlutusTx                             as PlutusTx
import           Language.PlutusTx.Coordination.Contracts.Game
import           Language.PlutusTx.Lattice
import qualified Language.PlutusTx.Prelude                     as PlutusTx
import           Ledger.Ada                                    (adaValueOf)
import           Spec.Lib                                      (timesFeeAdjust)
import qualified Spec.Lib                                      as Lib
import           Test.Tasty
import qualified Test.Tasty.HUnit                              as HUnit

w1, w2 :: Wallet
w1 = Wallet 1
w2 = Wallet 2

tests :: TestTree
tests = testGroup "game"
    [ checkPredicate @_ @ContractError "Expose 'lock' and 'guess' endpoints"
        game
        (endpointAvailable @"lock" w1 /\ endpointAvailable @"guess" w1)
        $ pure ()

    , checkPredicate @_ @ContractError "'lock' endpoint submits a transaction"
        game
        (anyTx w1)
        $ callEndpoint @"lock" w1 (LockParams "secret" (adaValueOf 10))

    , checkPredicate @_ @ContractError "'guess' endpoint is available after locking funds"
        game
        (endpointAvailable @"guess" w2)
        lockTrace

    , checkPredicate @_ @ContractError "guess right (unlock funds)"
        game
        (walletFundsChange w2 (1 `timesFeeAdjust` 10)
            /\ walletFundsChange w1 (1 `timesFeeAdjust` (-10)))
        guessTrace

    , checkPredicate @_ @ContractError "guess wrong"
        game
        (walletFundsChange w2 PlutusTx.zero
            /\ walletFundsChange w1 (1 `timesFeeAdjust` (-10)))
        guessWrongTrace
    , Lib.goldenPir "test/Spec/game.pir" $$(PlutusTx.compile [|| validateGuess ||])
    , HUnit.testCase "script size is reasonable" (Lib.reasonable gameValidator 20000)
    ]
