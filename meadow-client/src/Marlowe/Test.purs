module Marlowe.Test where

import Prelude
import Data.Array (cons, foldl)
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Lens (Lens', over, set)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.List (List)
import Data.Newtype (class Newtype, unwrap)
import Record (equal)
import Data.Set (Set)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Marlowe.Pretty (pretty)
import Marlowe.Semantics (AnyInput, ErrorResult, MApplicationResult(..), State, applyTransaction, emptyState)
import Marlowe.Types (BlockNumber, Contract(..), Person)

data Action
  = AdvanceBlocks BlockNumber
  | ApplyTransaction (Tuple (List AnyInput) (Set Person))

run :: Contract -> Array Action -> TestState
run contract actions = foldl applyAction (set (_Newtype <<< _contract) contract initialState) actions

newtype TestState
  = TestState
  { state :: State
  , moneyInContract :: BigInteger
  , blockNumber :: BlockNumber
  , contract :: Contract
  , errorResults :: Array ErrorResult
  }

derive instance genericTestState :: Generic TestState _

derive instance newtypeTestState :: Newtype TestState _

instance showTestState :: Show TestState where
  show (TestState ts) =
    "{ state: " <> show ts.state
      <> "\\n, moneyInContract: "
      <> show ts.moneyInContract
      <> "\\n, blockNumber: "
      <> show ts.blockNumber
      <> "\\n, errorResults: "
      <> show ts.errorResults
      <> "\\n, contract: \\n"
      <> (show <<< pretty) ts.contract

instance eqTestState :: Eq TestState where
  eq a b = equal (unwrap a) (unwrap b)

initialState :: TestState
initialState =
  TestState
    { state: emptyState
    , moneyInContract: zero
    , blockNumber: zero
    , contract: Null
    , errorResults: []
    }

_blockNumber :: forall s a. Lens' {blockNumber :: a | s} a
_blockNumber = prop (SProxy :: SProxy "blockNumber")

_moneyInContract :: forall s a. Lens' {moneyInContract :: a | s} a
_moneyInContract = prop (SProxy :: SProxy "moneyInContract")

_contract :: forall s a. Lens' {contract :: a | s} a
_contract = prop (SProxy :: SProxy "contract")

_state :: forall s a. Lens' {state :: a | s} a
_state = prop (SProxy :: SProxy "state")

_errorResults :: forall s a. Lens' {errorResults :: a | s} a
_errorResults = prop (SProxy :: SProxy "errorResults")

applyAction :: TestState -> Action -> TestState
applyAction testState (AdvanceBlocks n) = over (_Newtype <<< _blockNumber) (add n) testState

applyAction (TestState testState) (ApplyTransaction (Tuple inputs signatures)) = case applyTransaction inputs signatures testState.blockNumber testState.state testState.contract testState.moneyInContract of
  MSuccessfullyApplied {funds, state, contract} _ ->
    TestState $ testState
      # set _state state
      # set _moneyInContract funds
      # set _contract contract
  MCouldNotApply e -> TestState $ over _errorResults (cons e) testState
