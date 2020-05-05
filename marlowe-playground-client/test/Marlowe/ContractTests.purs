module Marlowe.ContractTests where

import Prelude
import Control.Monad.State (runState)
import Data.Array (snoc)
import Data.Integral (fromIntegral)
import Data.Lens (over, (^.))
import Data.Lens.NonEmptyList (_Head)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Examples.Marlowe.Contracts as Contracts
import Marlowe.Semantics (AccountId(..), ChoiceId(..), Contract(..), Input(..), Token(..), Party(..))
import Simulation.State (_contract, _pendingInputs, _transactionError, applyTransactions, updateContractInState, updateMarloweState)
import Simulation.Types (_marloweState, mkState)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)

all :: TestSuite
all =
  suite "Contract Tests" do
    test "Escrow" do
      -- A simple test that runs the Escrow contract to completion
      let
        ada = Token "" ""

        alice = "alice"

        bob = "bob"

        deposit = IDeposit (AccountId (fromIntegral 0) (Role alice)) (Role alice) ada (fromIntegral 450)

        choice = ChoiceId "choice"

        choice1 = IChoice (choice (Role alice)) (fromIntegral 0)

        choice2 = IChoice (choice (Role bob)) (fromIntegral 0)

        (Tuple _ finalState) =
          (flip runState mkState) do
            updateContractInState Contracts.escrow
            updateMarloweState (over _pendingInputs ((flip snoc) (Tuple deposit (Just alice))))
            applyTransactions
            updateMarloweState (over _pendingInputs ((flip snoc) (Tuple choice1 (Just alice))))
            updateMarloweState (over _pendingInputs ((flip snoc) (Tuple choice2 (Just bob))))
            applyTransactions

        finalContract = finalState ^. _marloweState <<< _Head <<< _contract

        txError = finalState ^. _marloweState <<< _Head <<< _transactionError
      equal Nothing txError
      equal (Just Close) finalContract
      pure unit
