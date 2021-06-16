-- TODO: Move these tests to marlowe-commons
module Marlowe.ContractTests where

import Prelude
import Control.Bind (bindFlipped)
import Control.Monad.Gen (class MonadGen, chooseInt, elements, oneOf)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (StateT, evalStateT, execState, get, gets, lift)
import Data.Array (length)
import Data.Array.NonEmpty (NonEmptyArray, fromArray)
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Either (Either(..), hush)
import Data.Int (round)
import Data.Lens (_Just, preview, previewOn, (^.))
import Data.Lens.NonEmptyList (_Head)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.NonEmpty ((:|))
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
import Marlowe.Holes (Term(..), fromTerm)
import Marlowe.Holes as T
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (Bound(..), ChoiceId(..), Contract(..), Input(..), Party(..), Token(..), TransactionError, TransactionWarning)
import Marlowe.Template (TemplateContent(..), fillTemplate)
import Partial.Unsafe (unsafePartial)
import SimulationPage.State (mkState)
import SimulationPage.Types as Simulation
import Simulator.Lenses (_SimulationRunning, _currentContract, _currentMarloweState, _currentPossibleActions, _executionState, _marloweState, _transactionError, _transactionWarnings)
import Simulator.State (applyInput, getAllActions, moveToSlot, startSimulation)
import Simulator.Types (ActionInput(..))
import Test.QuickCheck (Result(..))
import Test.QuickCheck.Gen (Gen)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Test.Unit.QuickCheck (quickCheck)
import Text.Pretty (pretty)

all :: TestSuite
all =
  suite "Contract Tests" do
    examplesMatch
    escrowSimpleFlow
    exampleContractsDontHaveErrors

-- We don't currently have a function that goes from semantic contract to term contract, so for the purposes
-- of this test we print it and parse it.
toTerm :: EM.Contract -> Term T.Contract
toTerm contract = unsafePartial $ fromJust $ hush $ parseContract $ show $ pretty contract

contractToExtended :: String -> Maybe EM.Contract
contractToExtended contract = case parseContract contract of -- We reuse the extended Marlowe parser for now since it is a superset
  Right parsedContract -> fromTerm parsedContract
  Left error -> Nothing

examplesMatch :: TestSuite
examplesMatch =
  suite "Purescript and Haskell examples match" do
    test "Simple escrow"
      $ equal (Just Escrow.fullExtendedContract) (contractToExtended Contracts.escrow)
    test "Escrow with collateral"
      $ equal (Just EscrowWithCollateral.fullExtendedContract) (contractToExtended Contracts.escrowWithCollateral)
    test "Zero coupon bond"
      $ equal (Just ZeroCouponBond.fullExtendedContract) (contractToExtended Contracts.zeroCouponBond)
    test "Coupon bond guaranteed"
      $ equal (Just CouponBondGuaranteed.extendedContract) (contractToExtended Contracts.couponBondGuaranteed)
    test "Swap"
      $ equal (Just Swap.fullExtendedContract) (contractToExtended Contracts.swap)
    test "Contract for differences"
      $ equal (Just ContractForDifferences.extendedContract) (contractToExtended Contracts.contractForDifferences)
    test "Contract for differences with oracle"
      $ equal (Just ContractForDifferencesWithOracle.extendedContract) (contractToExtended Contracts.contractForDifferencesWithOracle)

seller :: Party
seller = Role "Seller"

buyer :: Party
buyer = Role "Buyer"

arbiter :: Party
arbiter = Role "Arbiter"

ada :: Token
ada = Token "" ""

filledEscrow :: Term T.Contract
filledEscrow =
  toTerm
    ( fillTemplate
        ( TemplateContent
            { slotContent:
                Map.fromFoldable
                  [ "Buyer's deposit timeout" /\ BigInteger.fromInt 10
                  , "Buyer's dispute timeout" /\ BigInteger.fromInt 50
                  , "Seller's response timeout" /\ BigInteger.fromInt 100
                  , "Timeout for arbitrage" /\ BigInteger.fromInt 1000
                  ]
            , valueContent:
                Map.fromFoldable
                  [ "Price" /\ BigInteger.fromInt 450
                  ]
            }
        )
        Escrow.fullExtendedContract
    )

filledEscrowWithCollateral :: Term T.Contract
filledEscrowWithCollateral =
  toTerm
    ( fillTemplate
        ( TemplateContent
            { slotContent: mempty
            , valueContent:
                Map.fromFoldable
                  [ "Price" /\ BigInteger.fromInt 450
                  , "Collateral amount" /\ BigInteger.fromInt 500
                  ]
            }
        )
        EscrowWithCollateral.fixedTimeoutContract
    )

filledZeroCouponBond :: Term T.Contract
filledZeroCouponBond =
  toTerm
    ( fillTemplate
        ( TemplateContent
            { slotContent: mempty
            , valueContent:
                Map.fromFoldable
                  [ "Discounted price" /\ BigInteger.fromInt 100
                  , "Notional price" /\ BigInteger.fromInt 200
                  ]
            }
        )
        ZeroCouponBond.fixedTimeoutContract
    )

filledCouponBondGuaranteed :: Term T.Contract
filledCouponBondGuaranteed =
  toTerm
    ( fillTemplate
        ( TemplateContent
            { slotContent: mempty
            , valueContent:
                Map.fromFoldable
                  [ "Interest instalment" /\ BigInteger.fromInt 100
                  , "Principal" /\ BigInteger.fromInt 200
                  ]
            }
        )
        CouponBondGuaranteed.extendedContract
    )

filledSwap :: Term T.Contract
filledSwap =
  toTerm
    ( fillTemplate
        ( TemplateContent
            { slotContent: mempty
            , valueContent:
                Map.fromFoldable
                  [ "Amount of Ada" /\ BigInteger.fromInt 1500000
                  , "Amount of dollars" /\ BigInteger.fromInt 1
                  ]
            }
        )
        Swap.fixedTimeoutContract
    )

filledContractForDifferences :: Term T.Contract
filledContractForDifferences =
  toTerm
    ContractForDifferences.extendedContract

filledContractForDifferencesWithOracle :: Term T.Contract
filledContractForDifferencesWithOracle =
  toTerm
    ContractForDifferencesWithOracle.extendedContract

-- TODO:  We should combine this test with the ones defined in Marlowe.Holes.SemanticTest
--       so that we can have a single definition of contracts and flows, and then test what we care in each one. In semantic
--       test we care that the compute transaction of term and semantic are the same, in here we care about the output of the simulation.
escrowSimpleFlow :: TestSuite
escrowSimpleFlow =
  test "Escrow" do
    -- A simple test that runs the Escrow contract to completion
    let
      deposit = IDeposit seller buyer ada (BigInteger.fromInt 450)

      choice1 = IChoice ((ChoiceId "Report problem") buyer) (BigInteger.fromInt 1)

      choice2 = IChoice ((ChoiceId "Confirm problem") seller) (BigInteger.fromInt 1)

      finalState =
        (flip execState mkState) do
          startSimulation zero filledEscrow
          applyInput deposit
          applyInput choice1
          applyInput choice2

      finalContract = previewOn finalState _currentContract

      txError = do
        executionState <- preview (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning) finalState
        executionState ^. _transactionError
    equal Nothing txError
    equal (Just Close) (fromTerm =<< finalContract)
    pure unit

--
exampleContractsDontHaveErrors :: TestSuite
exampleContractsDontHaveErrors =
  suite "Provided Examples don't throw errors nor have warnings" do
    contractDontHaveErrors "Simple Escrow" filledEscrow
    contractDontHaveErrors "Escrow with collateral" filledEscrowWithCollateral
    contractDontHaveErrors "Zero coupon bond" filledZeroCouponBond
    contractDontHaveErrors "Coupon bond guaranteed" filledCouponBondGuaranteed
    contractDontHaveErrors "Swap" filledSwap
    contractDontHaveErrors "Contract for differences" filledContractForDifferences
    contractDontHaveErrors "Contract for differences with oracle" filledContractForDifferencesWithOracle

-- This is a property based test that checks that for a given contract, the possible actions available
-- during the simulation don't throw errors nor warnings.
contractDontHaveErrors :: String -> Term T.Contract -> TestSuite
contractDontHaveErrors contractName contract =
  test contractName
    $ quickCheck
    $ evalStateT property mkState
  where
  property :: StateT Simulation.State Gen Result
  property = do
    startSimulation zero contract
    runContract (Just contract)

  -- When the possible action is a Choose, we need to generate a random value inside the provided Bound.
  -- We use this function (which looses precision) in order to select a small integer and wrap it in a BigInteger
  looselyToInt :: BigInteger -> Int
  looselyToInt = round <<< BigInteger.toNumber

  genValueInBound :: forall m. MonadGen m => MonadRec m => Bound -> m BigInteger
  genValueInBound (Bound from to) = BigInteger.fromInt <$> chooseInt (looselyToInt from) (looselyToInt to)

  runContract :: Maybe (Term T.Contract) -> StateT Simulation.State Gen Result
  runContract Nothing = pure Success

  runContract (Just (Term T.Close _)) = pure Success

  -- TODO: For the moment it was not needed, as none of the examples triggered a warning nor an error
  --       but we should add an extra parameter to runContract that includes the current Action list
  --       and in case of a failure, we should print what is the list that causes the problem.
  runContract (Just _) = do
    simulationState <- get
    let
      mPossibleActions :: Maybe (NonEmptyArray ActionInput)
      mPossibleActions =
        simulationState
          # preview _currentPossibleActions
          # map getAllActions
          # bindFlipped fromArray
    case mPossibleActions of
      Nothing -> pure $ Failed "no available actions"
      Just possibleActions -> do
        action <- lift $ elements possibleActions
        case action of
          MoveToSlot slot -> moveToSlot slot
          DepositInput accountId party token value -> applyInput $ IDeposit accountId party token value
          ChoiceInput choiceId bounds value -> do
            randomValue <- lift $ oneOf $ pure value :| (genValueInBound <$> bounds)
            applyInput $ IChoice choiceId randomValue
          NotifyInput -> applyInput INotify
        (mError :: Maybe TransactionError) <- gets $ preview (_currentMarloweState <<< _executionState <<< _SimulationRunning <<< _transactionError <<< _Just)
        (mWarnings :: Maybe (Array TransactionWarning)) <- gets $ preview (_currentMarloweState <<< _executionState <<< _SimulationRunning <<< _transactionWarnings)
        mContract <- gets (preview _currentContract)
        case mError, mWarnings of
          Just err, _ -> pure $ Failed "it has errors"
          _, Just warnings
            | length warnings > 0 -> pure $ Failed "it has warnings"
          _, _ -> runContract mContract
