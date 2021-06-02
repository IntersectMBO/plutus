module Marlowe.ContractTests where

import Prelude
import Control.Monad.State (runState)
import Data.Array (snoc)
import Data.BigInteger (fromInt)
import Data.Either (Either(..), hush)
import Data.Foldable (for_)
import Data.Lens (over, preview, previewOn, set, (^.))
import Data.Lens.NonEmptyList (_Head)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Examples.Marlowe.Contracts as Contracts
import Examples.PureScript.ContractForDifferences as ContractForDifferences
import Examples.PureScript.ContractForDifferencesWithOracle as ContractForDifferencesWithOracle
import Examples.PureScript.CouponBondGuaranteed as CouponBondGuaranteed
import Examples.PureScript.Escrow as Escrow
import Examples.PureScript.EscrowWithCollateral as EscrowWithCollateral
import Examples.PureScript.Swap as Swap
import Examples.PureScript.ZeroCouponBond as ZeroCouponBond
import Marlowe.Extended as EM
import Marlowe.Holes (Term, fromTerm)
import Marlowe.Holes as T
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (ChoiceId(..), Contract(..), Input(..), Party(..), Token(..))
import Marlowe.Template (TemplateContent(..), fillTemplate)
import SimulationPage.State (mkState)
import Simulator.Lenses (_SimulationRunning, _currentContract, _executionState, _marloweState, _pendingInputs, _transactionError)
import Simulator.State (applyTransactions, updateMarloweState, emptyExecutionStateWithSlot)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (assertFalse, equal)
import Text.Pretty (pretty)

contractToExtended :: String -> Maybe EM.Contract
contractToExtended contract = case parseContract contract of -- We reuse the extended Marlowe parser for now since it is a superset
  Right parsedContract -> fromTerm parsedContract
  Left error -> Nothing

-- TODO: Move these tests to marlowe-commons
all :: TestSuite
all =
  suite "Contract Tests" do
    test "Purescript and Haskell examples match" do
      equal (Just Escrow.fullExtendedContract) (contractToExtended Contracts.escrow)
      equal (Just EscrowWithCollateral.fullExtendedContract) (contractToExtended Contracts.escrowWithCollateral)
      equal (Just ZeroCouponBond.fullExtendedContract) (contractToExtended Contracts.zeroCouponBond)
      equal (Just CouponBondGuaranteed.extendedContract) (contractToExtended Contracts.couponBondGuaranteed)
      equal (Just Swap.fullExtendedContract) (contractToExtended Contracts.swap)
      equal (Just ContractForDifferences.extendedContract) (contractToExtended Contracts.contractForDifferences)
      equal (Just ContractForDifferencesWithOracle.extendedContract) (contractToExtended Contracts.contractForDifferencesWithOracle)
      pure unit
    test "Escrow" do
      -- A simple test that runs the Escrow contract to completion
      let
        -- TODO: We don't currently have a function that goes from semantic contract to term contract, so for the purposes
        --       of this test we print it and parse it. We should combine this test with the ones defined in Marlowe.Holes.SemanticTest
        --       so that we can have a single definition of contracts and flows, and then test what we care in each one. In semantic
        --       test we care that the compute transaction of term and semantic are the same, in here we care about the output of the simulation.
        mFilledEscrow :: Maybe (Term T.Contract)
        mFilledEscrow =
          hush $ parseContract $ show
            $ pretty
                ( fillTemplate
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
                    Escrow.fullExtendedContract
                )

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
      equal (Just Close) (fromTerm =<< finalContract)
      pure unit
