module Marlowe.ContractTests where

import Prelude
import Control.Monad.State (runState)
import Data.Array (snoc)
import Data.BigInteger (fromInt)
import Data.Either (Either(..))
import Data.Lens (over, preview, previewOn, set, (^.))
import Data.Lens.NonEmptyList (_Head)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Examples.Marlowe.Contracts as Contracts
import Marlowe.Extended (TemplateContent(..), fillTemplate, toCore)
import Marlowe.Extended as EM
import Marlowe.Holes (fromTerm)
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (ChoiceId(..), Contract(..), Input(..), Party(..), Token(..))
import SimulationPage.Types (_SimulationRunning, _currentContract, _executionState, _marloweState, _pendingInputs, _transactionError, emptyExecutionStateWithSlot, mkState)
import Simulator (applyTransactions, updateMarloweState)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (assertFalse, equal)

all :: TestSuite
all =
  suite "Contract Tests" do
    test "Escrow" do
      -- A simple test that runs the Escrow contract to completion
      let
        filledEscrow = case parseContract Contracts.escrow of -- We reuse the extended Marlowe parser for now since it is a superset 
          Right parsedContract -> case fromTerm parsedContract of
            Just extendedContract -> case toCore
                ( ( fillTemplate
                      ( TemplateContent
                          { slotContent:
                              Map.fromFoldable
                                [ "Buyer's deposit timeout" /\ fromInt 10
                                , "Buyer's dispute timeout" /\ fromInt 50
                                , "Seller's response timeout" /\ fromInt 100
                                , "Timeout for arbitrage" /\ fromInt 1000
                                ]
                          , valueContent:
                              Map.fromFoldable
                                [ "Price" /\ fromInt 450
                                ]
                          }
                      )
                      extendedContract
                  ) ::
                    EM.Contract
                ) of
              Just contract -> contract
              Nothing -> Close
            Nothing -> Close
          Left error -> Close

        ada = Token "" ""

        buyer = "Buyer"

        seller = "Seller"

        deposit = IDeposit (Role seller) (Role buyer) ada (fromInt 450)

        choice1 = IChoice ((ChoiceId "Report problem") (Role buyer)) (fromInt 1)

        choice2 = IChoice ((ChoiceId "Confirm problem") (Role seller)) (fromInt 1)

        (Tuple _ finalState) =
          (flip runState mkState) do
            updateMarloweState (set _executionState (emptyExecutionStateWithSlot zero filledEscrow))
            updateMarloweState (over (_executionState <<< _SimulationRunning <<< _pendingInputs) ((flip snoc) deposit))
            applyTransactions
            updateMarloweState (over (_executionState <<< _SimulationRunning <<< _pendingInputs) ((flip snoc) choice1))
            updateMarloweState (over (_executionState <<< _SimulationRunning <<< _pendingInputs) ((flip snoc) choice2))
            applyTransactions

        finalContract = previewOn finalState _currentContract

        txError = do
          executionState <- preview (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning) finalState
          executionState ^. _transactionError
      assertFalse "Could not instantiate Escrow contract" (filledEscrow == Close)
      equal Nothing txError
      equal (Just Close) finalContract
      pure unit
