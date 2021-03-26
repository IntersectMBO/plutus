module Marlowe.ContractTests where

import Prelude
import Control.Monad.State (runState)
import Data.Array (snoc)
import Data.BigInteger (fromInt)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (over, preview, previewOn, set, (^.))
import Data.Lens.NonEmptyList (_Head)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Examples.Marlowe.Contracts as Contracts
import Marlowe.Extended (TemplateContent(..), fillTemplate, toCore)
import Marlowe.Extended as EM
import Marlowe.Holes (fromTerm)
import Marlowe.Market.Contract1 as Contract1
import Marlowe.Market.Contract2 as Contract2
import Marlowe.Market.Contract3 as Contract3
import Marlowe.Market.Contract4 as Contract4
import Marlowe.Market.Contract5 as Contract5
import Marlowe.Market.Contract6 as Contract6
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (ChoiceId(..), Contract(..), Input(..), Party(..), Token(..))
import SimulationPage.Types (_SimulationRunning, _currentContract, _executionState, _marloweState, _pendingInputs, _transactionError, emptyExecutionStateWithSlot, mkState)
import Simulator (applyTransactions, updateMarloweState)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (assertFalse, equal)

contractToExtended :: String -> Maybe EM.Contract
contractToExtended contract = case parseContract contract of -- We reuse the extended Marlowe parser for now since it is a superset 
  Right parsedContract -> fromTerm parsedContract
  Left error -> Nothing

all :: TestSuite
all =
  suite "Contract Tests" do
    test "Purescript and Haskell examples match" do
      equal (Just Contract1.extendedContract) (contractToExtended Contracts.escrow)
      equal (Just Contract2.extendedContract) (contractToExtended Contracts.escrowWithCollateral)
      equal (Just Contract3.extendedContract) (contractToExtended Contracts.zeroCouponBond)
      equal (Just Contract4.extendedContract) (contractToExtended Contracts.couponBondGuaranteed)
      equal (Just Contract5.extendedContract) (contractToExtended Contracts.swap)
      equal (Just Contract6.extendedContract) (contractToExtended Contracts.contractForDifferences)
      pure unit
    test "Escrow" do
      -- A simple test that runs the Escrow contract to completion
      let
        mFilledEscrow :: Maybe Contract
        mFilledEscrow =
          maybe Nothing
            ( toCore
                <<< ( fillTemplate
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
                  )
            )
            (contractToExtended Contracts.escrow)

        ada = Token "" ""

        buyer = "Buyer"

        seller = "Seller"

        deposit = IDeposit (Role seller) (Role buyer) ada (fromInt 450)

        choice1 = IChoice ((ChoiceId "Report problem") (Role buyer)) (fromInt 1)

        choice2 = IChoice ((ChoiceId "Confirm problem") (Role seller)) (fromInt 1)

        (Tuple _ finalState) =
          (flip runState mkState)
            $ for_ mFilledEscrow \filledEscrow -> do
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
      assertFalse "Could not instantiate Escrow contract" (mFilledEscrow == Nothing)
      equal Nothing txError
      equal (Just Close) finalContract
      pure unit
