 {-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
module Spec.Game(tests) where

import           Language.Plutus.Contract.Test
import qualified Language.Plutus.Contract.Effects.ExposeEndpoint as Endpoint
import qualified Language.PlutusTx                               as PlutusTx
import qualified Language.PlutusTx.Prelude                       as PlutusTx
import           Language.PlutusTx.Lattice
import qualified Language.Plutus.Contract.Request                as R
import           Language.PlutusTx.Coordination.Contracts.Game
import qualified Spec.Lib                                      as Lib
import           Spec.Lib                                      (timesFeeAdjust)
import           Test.Tasty
import qualified Test.Tasty.HUnit                              as HUnit

w1, w2 :: Wallet
w1 = Wallet 1
w2 = Wallet 2

tests :: TestTree
tests = testGroup "game"
    [ checkPredicate @_ @R.ContractError "Expose 'lock' and 'guess' endpoints"
        game
        (endpointAvailable @"lock" w1 /\ endpointAvailable @"guess" w1)
        $ pure ()

    , checkPredicate @_ @R.ContractError "'lock' endpoint submits a transaction"
        game
        (anyTx w1)
        $ addEvent w1 (Endpoint.event @"lock" (LockParams "secret" 10))

    , checkPredicate @_ @R.ContractError "'guess' endpoint is available after locking funds"
        game
        (endpointAvailable @"guess" w2)
        lockTrace

    , checkPredicate @_ @R.ContractError "guess right (unlock funds)"
        game
        (walletFundsChange w2 (1 `timesFeeAdjust` 10)
            /\ walletFundsChange w1 (1 `timesFeeAdjust` (-10)))
        guessTrace

    , checkPredicate @_ @R.ContractError "guess wrong"
        game
        (walletFundsChange w2 PlutusTx.zero
            /\ walletFundsChange w1 (1 `timesFeeAdjust` (-10)))
        guessWrongTrace
    , Lib.goldenPir "test/Spec/game.pir" $$(PlutusTx.compile [|| validateGuess ||])
    , HUnit.testCase "script size is reasonable" (Lib.reasonable gameValidator 15000)
    ]
