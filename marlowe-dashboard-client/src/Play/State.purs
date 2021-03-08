module Play.State
  ( mkInitialState
  , handleAction
  ) where

import Prelude
import Contract.Lenses (_executionState)
import Contract.State (defaultState, handleAction) as Contract
import Contract.Types (Action(..)) as Contract
import Control.Monad.Reader (class MonadAsk)
import Control.Monad.State.Class (get)
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
import Marlowe.Execution (_contract)
import Marlowe.Extended (fillTemplate, toCore)
import Play.Lenses (_contractState, _menuOpen, _templateState)
import Play.Types (Action(..), Card(..), ContractStatus(..), Screen(..), State)
import Template.Lenses (_extendedContract, _template, _templateContent)
import Template.State (defaultState, handleAction, mkInitialState) as Template
import Template.Types (Action(..), Screen(..)) as Template
import WalletData.Types (WalletDetails)

mkInitialState :: WalletDetails -> State
mkInitialState walletDetails =
  { walletDetails: walletDetails
  , menuOpen: false
  , screen: ContractsScreen Running
  , card: Nothing
  , templateState: Template.defaultState
  , contractState: Contract.defaultState
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
  for_ previousCard $ const $ assign (_playState <<< _menuOpen) false

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
  handleAction $ SetScreen $ TemplateScreen Template.ContractRolesScreen

handleAction (TemplateAction (Template.SetScreen screen)) = handleAction $ SetScreen $ TemplateScreen screen

handleAction (TemplateAction Template.ToggleTemplateLibraryCard) = handleAction $ ToggleCard TemplateLibraryCard

handleAction (TemplateAction Template.ToggleSetupConfirmationCard) = handleAction $ ToggleCard ContractSetupConfirmationCard

handleAction (TemplateAction Template.StartContract) = do
  mTemplateState <- peruse (_playState <<< _templateState)
  for_ mTemplateState \templateState ->
    let
      extendedContract = view (_template <<< _extendedContract) templateState

      templateContent = view _templateContent templateState

      mContract = toCore $ fillTemplate templateContent extendedContract
    in
      for_ mContract \contract -> do
        assign (_playState <<< _contractState <<< _executionState <<< _contract) contract
        handleAction $ SetScreen $ ContractsScreen Running
        handleAction $ ToggleCard ContractCard

-- other template actions
handleAction (TemplateAction templateAction) = Template.handleAction templateAction

-- contract actions that need to be handled here
handleAction (ContractAction (Contract.ToggleTemplateLibraryCard)) = handleAction $ ToggleCard TemplateLibraryCard

-- other contract actions
handleAction (ContractAction contractAction) = do
  state <- get
  mapMaybeSubmodule state (_playState <<< _contractState) (MainFrame.PlayAction <<< ContractAction) Contract.defaultState (Contract.handleAction contractAction)

-- all other actions are handled in `MainFrame.State`
handleAction _ = pure unit
