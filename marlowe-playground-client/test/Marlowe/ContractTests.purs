module Marlowe.ContractTests where

import Prelude

import Control.Monad.State (class MonadState, StateT, runState)
import Data.Array (snoc)
import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.Integral (fromIntegral)
import Data.Lens (modifying, over, use, (^.))
import Data.List.NonEmpty as NEL
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Tuple (Tuple(..))
import Examples.Marlowe.Contracts as Contracts
import Marlowe.Semantics (AccountId(..), Ada(..), ChoiceId(..), Contract(..), Input(..))
import MonadApp (class MonadApp, applyTransactions, extendWith, marloweEditorSetAnnotations, updateContractInState, updateContractInStateP, updateMarloweState, updatePossibleActions, updateStateP)
import Network.RemoteData (RemoteData(..))
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Types (FrontendState(..), View(..), _Head, _contract, _currentMarloweState, _editorErrors, _marloweState, _pendingInputs, _transactionError, emptyMarloweState)

-- | For these tests we only need to worry about the MarloweState that is being carried around
--   However we can use similar techniques to mock other parts of the App
newtype MockApp a = MockApp (StateT FrontendState Identity a)

derive instance newtypeMockApp :: Newtype (MockApp a) _

derive newtype instance functorMockApp :: Functor MockApp

derive newtype instance applicativeMockApp :: Applicative MockApp

derive newtype instance applyMockApp :: Apply MockApp

derive newtype instance bindMockApp :: Bind MockApp

derive newtype instance monadMockApp :: Monad MockApp

derive newtype instance monadStateMockApp :: MonadState FrontendState MockApp

instance monadAppState :: MonadApp MockApp where
  haskellEditorSetValue _ _ = pure unit
  haskellEditorGetValue = pure Nothing
  haskellEditorSetAnnotations _ = pure unit
  haskellEditorGotoLine _ _ = pure unit
  marloweEditorSetValue _ _ = pure unit
  marloweEditorGetValue = pure (Just Contracts.escrow)
  marloweEditorSetAnnotations _ = pure unit
  preventDefault _ = pure unit
  readFileFromDragEvent _ = pure ""
  updateContractInState contract = do
    updateContractInStateImpl contract
    annotations <- use (_marloweState <<< _Head <<< _editorErrors)
    marloweEditorSetAnnotations annotations
  updateState = do
    -- saveInitialStateImpl
    wrap $ modifying _currentMarloweState updateStateP
  saveInitialState = pure unit -- saveInitialStateImpl
  updateMarloweState f = wrap $ modifying _marloweState (extendWith f)
  applyTransactions = wrap $ modifying _marloweState (extendWith updateStateP)
  resetContract = pure unit
  saveBuffer _ = pure unit
  saveMarloweBuffer _ = pure unit
  getOauthStatus = pure Loading
  getGistByGistId _ = pure Loading
  postGist _ = pure Loading
  patchGistByGistId _ _ = pure Loading
  postContractHaskell _ = pure Loading
  resizeBlockly = pure Nothing
  setBlocklyCode _ = pure unit
  checkContractForWarnings _ = pure unit

updateContractInStateImpl :: String -> MockApp Unit
updateContractInStateImpl contract = modifying _currentMarloweState (updatePossibleActions <<< updateContractInStateP contract)

initialState :: FrontendState
initialState =
  FrontendState
    { view: HaskellEditor
    , compilationResult: NotAsked
    , marloweCompileResult: Right unit
    , authStatus: NotAsked
    , createGistResult: NotAsked
    , marloweState: NEL.singleton (emptyMarloweState zero)
    , oldContract: Nothing
    , gistUrl: Nothing
    , blocklyState: Nothing
    , analysisState: NotAsked
    }

runTests :: forall a. MockApp a -> Tuple a FrontendState
runTests app = runState (unwrap app) initialState

all :: TestSuite
all =
  suite "Contract Tests" do
    test "Escrow" do
        -- A simple test that runs the Escrow contract to completion
        let alice = "alice"
            bob = "bob"
            deposit = IDeposit (AccountId (fromIntegral 0) alice) alice (Lovelace (fromIntegral 450))
            choice = ChoiceId "choice"
            choice1 = IChoice (choice alice) (fromIntegral 0)
            choice2 = IChoice (choice bob) (fromIntegral 0)
            (Tuple _ finalState) = runTests $ do
                updateContractInState Contracts.escrow
                updateMarloweState (over _pendingInputs ((flip snoc) (Tuple deposit alice)))
                applyTransactions
                updateMarloweState (over _pendingInputs ((flip snoc) (Tuple choice1 alice)))
                updateMarloweState (over _pendingInputs ((flip snoc) (Tuple choice2 bob)))
                applyTransactions
            finalContract = finalState ^. _marloweState <<< _Head <<< _contract
            txError = finalState ^. _marloweState <<< _Head <<< _transactionError
        equal Nothing txError
        equal (Just Close) finalContract
        pure unit
