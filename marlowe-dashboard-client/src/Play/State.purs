module Play.State
  ( mkInitialState
  , handleQuery
  , handleAction
  ) where

import Prelude
import Bridge (toFront)
import Capability.Contract (class MonadContract)
import Capability.Wallet (class MonadWallet)
import Contract.State (defaultState, handleAction) as Contract
import Contract.State (instantiateExtendedContract)
import Contract.Types (Action(..), State) as Contract
import ContractHome.Lenses (_contracts)
import ContractHome.State (defaultState, handleAction) as ContractHome
import ContractHome.Types (Action(..), State) as ContractHome
import Control.Monad.Reader (class MonadAsk)
import Data.Foldable (for_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Lens (assign, modifying, set, (^.))
import Data.Lens.Extra (peruse)
import Data.Lens.Prism.Maybe (_Just)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set.Extra (setToMap)
import Data.Time.Duration (Minutes)
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM, modify_)
import Halogen.Extra (mapMaybeSubmodule)
import MainFrame.Lenses (_card, _playState, _screen)
import MainFrame.Types (Action(..), State) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.HasParties (getParties)
import Marlowe.Semantics (Party(..), Slot)
import Marlowe.Semantics as Semantic
import Play.Lenses (_contractsState, _currentSlot, _menuOpen, _selectedContract, _templateState, _walletDetails)
import Play.Types (Action(..), Card(..), Screen(..), State)
import Plutus.PAB.Webserver.Types (CombinedWSStreamToClient(..))
import Template.Lenses (_extendedContract, _metaData, _roleWallets, _template, _templateContent)
import Template.State (defaultState, handleAction, mkInitialState) as Template
import Template.Types (Action(..)) as Template
import WalletData.Lenses (_assets, _wallet)
import WalletData.Types (WalletDetails, WalletNickname)

toContractHome ::
  forall m msg slots.
  Functor m =>
  HalogenM ContractHome.State ContractHome.Action slots msg m Unit ->
  HalogenM MainFrame.State MainFrame.Action slots msg m Unit
toContractHome = mapMaybeSubmodule (_playState <<< _contractsState) (MainFrame.PlayAction <<< ContractHomeAction) ContractHome.defaultState

toContract ::
  forall m msg slots.
  Functor m =>
  HalogenM Contract.State Contract.Action slots msg m Unit ->
  HalogenM MainFrame.State MainFrame.Action slots msg m Unit
toContract = mapMaybeSubmodule (_playState <<< _selectedContract) (MainFrame.PlayAction <<< ContractAction) Contract.defaultState

mkInitialState :: WalletDetails -> Slot -> Minutes -> State
mkInitialState walletDetails currentSlot timezoneOffset =
  { walletDetails: walletDetails
  , menuOpen: false
  , screen: ContractsScreen
  , card: Nothing
  , currentSlot
  , timezoneOffset
  , templateState: Template.defaultState
  , contractsState: ContractHome.defaultState
  }

handleQuery ::
  forall m.
  CombinedWSStreamToClient -> HalogenM MainFrame.State MainFrame.Action ChildSlots Msg m Unit
handleQuery (InstanceUpdate contractInstanceId instanceStatusToClient) = pure unit

handleQuery (SlotChange slot) = assign (_playState <<< _currentSlot) $ toFront slot

handleQuery (WalletFundsChange wallet value) = do
  mCurrentWallet <- peruse (_playState <<< _walletDetails <<< _wallet)
  for_ mCurrentWallet \currentWallet ->
    when (currentWallet == toFront wallet)
      $ assign (_playState <<< _walletDetails <<< _assets) (toFront value)

-- Some actions are handled in `MainFrame.State` because they involve
-- modifications of that state. See Note [State].
handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  MonadContract m =>
  MonadWallet m =>
  Action -> HalogenM MainFrame.State MainFrame.Action ChildSlots Msg m Unit
handleAction ToggleMenu = modifying (_playState <<< _menuOpen) not

handleAction (SetScreen screen) =
  modify_
    $ set (_playState <<< _menuOpen) false
    <<< set (_playState <<< _card) Nothing
    <<< set (_playState <<< _screen) screen

handleAction (SetCard card) = do
  previousCard <- peruse (_playState <<< _card)
  assign (_playState <<< _card) card

handleAction (ToggleCard card) = do
  mCurrentCard <- peruse (_playState <<< _card <<< _Just)
  case mCurrentCard of
    Just currentCard
      | currentCard == card -> handleAction $ SetCard Nothing
    _ -> handleAction $ SetCard $ Just card

handleAction (SetCurrentSlot currentSlot) = do
  toContractHome $ ContractHome.handleAction $ ContractHome.AdvanceTimedOutContracts currentSlot
  modify_
    $ set (_playState <<< _currentSlot) currentSlot

-- template actions that need to be handled here
handleAction (TemplateAction (Template.SetTemplate template)) = do
  mCurrentTemplate <- peruse (_playState <<< _templateState <<< _template)
  when (mCurrentTemplate /= Just template) $ assign (_playState <<< _templateState) $ Template.mkInitialState template
  handleAction $ SetScreen TemplateScreen

handleAction (TemplateAction Template.ToggleTemplateLibraryCard) = handleAction $ ToggleCard TemplateLibraryCard

handleAction (TemplateAction (Template.ToggleCreateWalletCard tokenName)) = handleAction $ ToggleCard $ CreateWalletCard $ Just tokenName

handleAction (TemplateAction Template.ToggleSetupConfirmationCard) = handleAction $ ToggleCard ContractSetupConfirmationCard

-- NOTE:  This handler makes works with the assumption than the contract was created from the template functionality
--        but that will only be the case for the person setting up the contract. Once we connect the backend, and a
--        contract is created by another participant, we won't be dealing with Extended contracts but actually
--        Semantic contracts and specially we won't have the roleWallets.
handleAction (TemplateAction Template.StartContract) = do
  mPlayState <- peruse _playState
  for_ mPlayState \playState -> do
    let
      templateState = playState ^. _templateState

      extendedContract = templateState ^. (_template <<< _extendedContract)

      templateContent = templateState ^. _templateContent

      metadata = templateState ^. (_template <<< _metaData)

      currentSlot = playState ^. _currentSlot

      participants :: Map Semantic.Party (Maybe WalletNickname)
      participants =
        mapWithIndex
          ( \party _ -> case party of
              PK _ -> Nothing
              Role roleName -> Map.lookup roleName (templateState ^. _roleWallets)
          )
          (setToMap $ getParties extendedContract)

      -- FIXME: Need to see how do I tie the current user to a role in the contract
      mActiveUserParty = Nothing

      -- FIXME: the contract id should be the result of calling the PAB
      contractId = "FIXME need a contract id"

      -- TODO: get walletIDs from nicknames in roleWallets
      -- TODO: pass these walletIDs along with the contract to the PAB to start the contract
      mContractState = instantiateExtendedContract contractId currentSlot extendedContract templateContent metadata participants mActiveUserParty
    for_ mContractState \contractState -> do
      modifying (_playState <<< _contractsState <<< _contracts) (Map.insert contractId contractState)
      handleAction $ SetScreen $ ContractsScreen
      toContractHome $ ContractHome.handleAction $ ContractHome.OpenContract contractId

-- other template actions
handleAction (TemplateAction templateAction) = Template.handleAction templateAction

-- contract home actions that need to be handled here
handleAction (ContractHomeAction (ContractHome.ToggleTemplateLibraryCard)) = handleAction $ ToggleCard TemplateLibraryCard

handleAction (ContractHomeAction a@(ContractHome.OpenContract _)) = do
  toContractHome $ ContractHome.handleAction a
  handleAction $ ToggleCard ContractCard

-- other contract home actions
handleAction (ContractHomeAction contractAction) = void $ toContractHome $ ContractHome.handleAction contractAction

-- contract actions that need to be handled here
-- FIXME: instead of toggle card I need to implement a card stack and add it to the stack
handleAction (ContractAction (Contract.AskConfirmation action)) = handleAction $ ToggleCard $ ContractActionConfirmationCard action

-- FIXME: Once we have card stack this action should not be necesary
handleAction (ContractAction (Contract.ConfirmAction action)) = do
  void $ toContract $ Contract.handleAction $ Contract.ConfirmAction action
  handleAction $ ToggleCard ContractCard

-- FIXME: instead of ToggleCard I need to implement a card stack and pop the stack
handleAction (ContractAction Contract.CancelConfirmation) = handleAction $ ToggleCard ContractCard

-- other contract  actions
handleAction (ContractAction contractAction) = void $ toContract $ Contract.handleAction contractAction

-- all other actions are handled in `MainFrame.State`
handleAction _ = pure unit
