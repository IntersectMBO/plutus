module Play.State
  ( mkInitialState
  , handleAction
  ) where

import Prelude
import Contract.State (defaultState, handleAction, mkInitialState) as Contract
import Contract.Types (Action, State) as Contract
import ContractHome.Lenses (_contracts, _selectedContract)
import ContractHome.State (defaultState, handleAction) as ContractHome
import ContractHome.Types (Action(..), State) as ContractHome
import Control.Monad.Reader (class MonadAsk)
import Data.Array as Array
import Data.Foldable (for_)
import Data.Lens (assign, modifying, set, view)
import Data.Lens.Extra (peruse)
import Data.Lens.Prism.Maybe (_Just)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM, modify_)
import Halogen.Extra (mapMaybeSubmodule)
import MainFrame.Lenses (_card, _playState, _screen)
import MainFrame.Types (Action(..), State) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Extended (fillTemplate, toCore)
import Play.Lenses (_contractsState, _menuOpen, _templateState)
import Play.Types (Action(..), Card(..), Screen(..), State)
import Template.Lenses (_extendedContract, _metaData, _template, _templateContent)
import Template.State (defaultState, handleAction, mkInitialState) as Template
import Template.Types (Action(..)) as Template
import WalletData.Types (WalletDetails)

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
toContract = mapMaybeSubmodule (_playState <<< _contractsState <<< _selectedContract <<< _Just) (MainFrame.PlayAction <<< ContractAction) $ Contract.defaultState

mkInitialState :: WalletDetails -> State
mkInitialState walletDetails =
  { walletDetails: walletDetails
  , menuOpen: false
  , screen: ContractsScreen
  , card: Nothing
  , templateState: Template.defaultState
  , contractsState: ContractHome.defaultState
  }

-- Some actions are handled in `MainFrame.State` because they involve
-- modifications of that state. See Note [State].
handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
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

-- template actions that need to be handled here
handleAction (TemplateAction (Template.SetTemplate template)) = do
  mCurrentTemplate <- peruse (_playState <<< _templateState <<< _template)
  when (mCurrentTemplate /= Just template) $ assign (_playState <<< _templateState) $ Template.mkInitialState template
  handleAction $ SetScreen TemplateScreen

handleAction (TemplateAction Template.ToggleTemplateLibraryCard) = handleAction $ ToggleCard TemplateLibraryCard

handleAction (TemplateAction Template.ToggleSetupConfirmationCard) = handleAction $ ToggleCard ContractSetupConfirmationCard

handleAction (TemplateAction Template.StartContract) = do
  mTemplateState <- peruse (_playState <<< _templateState)
  for_ mTemplateState \templateState ->
    let
      extendedContract = view (_template <<< _extendedContract) templateState

      templateContent = view _templateContent templateState

      metadata = view (_template <<< _metaData) templateState

      mContract = toCore $ fillTemplate templateContent extendedContract
    in
      for_ mContract \contract -> do
        let
          contractState = Contract.mkInitialState zero contract metadata
        modifying (_playState <<< _contractsState <<< _contracts) (Array.cons contractState)
        toContractHome $ ContractHome.handleAction $ ContractHome.OpenContract contractState
        handleAction $ SetScreen $ ContractsScreen
        handleAction $ ToggleCard ContractCard

-- other template actions
handleAction (TemplateAction templateAction) = Template.handleAction templateAction

-- contract home actions that need to be handled here
handleAction (ContractHomeAction (ContractHome.ToggleTemplateLibraryCard)) = handleAction $ ToggleCard TemplateLibraryCard

handleAction (ContractHomeAction a@(ContractHome.OpenContract _)) = do
  toContractHome $ ContractHome.handleAction a
  handleAction $ ToggleCard ContractCard

-- other contract home actions
handleAction (ContractHomeAction contractAction) = void $ toContractHome $ ContractHome.handleAction contractAction

-- All contract actions are handled by the subcomponent for the moment
handleAction (ContractAction contractAction) = void $ toContract $ Contract.handleAction contractAction

-- all other actions are handled in `MainFrame.State`
handleAction _ = pure unit
