module Play.State
  ( dummyState
  , mkInitialState
  , handleAction
  ) where

import Prelude
import Capability.Contract (class ManageContract)
import Capability.Toast (class Toast)
import Capability.Wallet (class ManageWallet)
import Contract.State (dummyState, handleAction) as Contract
import Contract.State (instantiateExtendedContract)
import Contract.Types (Action(..), State) as Contract
import ContractHome.Lenses (_contracts)
import ContractHome.State (dummyState, handleAction) as ContractHome
import ContractHome.Types (Action(..), State) as ContractHome
import Control.Monad.Reader (class MonadAsk)
import Data.Array (init, snoc)
import Data.Foldable (for_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Lens (assign, modifying, set, use, (^.))
import Data.Lens.Extra (peruse)
import Data.Lens.Fold (lastOf)
import Data.Lens.Traversal (traversed)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set.Extra (setToMap)
import Data.Time.Duration (Minutes(..))
import Data.UUID (emptyUUID)
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM, modify_)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import MainFrame.Lenses (_screen)
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.HasParties (getParties)
import Marlowe.Semantics (Party(..), Slot)
import Marlowe.Semantics as Semantic
import Play.Lenses (_cards, _contractsState, _currentSlot, _menuOpen, _selectedContract, _templateState)
import Play.Types (Action(..), Card(..), Screen(..), State)
import Template.Lenses (_extendedContract, _metaData, _roleWallets, _template, _templateContent)
import Template.State (dummyState, handleAction, mkInitialState) as Template
import Template.Types (Action(..), State) as Template
import Types (ContractInstanceId(..))
import WalletData.Types (PubKeyHash(..), Wallet(..), WalletDetails, WalletNickname)

-- see note [dummyState]
dummyState :: State
dummyState = mkInitialState defaultWalletDetails zero $ Minutes zero
  where
  defaultWalletDetails =
    { walletNickname: mempty
    , contractInstanceId: ContractInstanceId emptyUUID
    , wallet: Wallet zero
    , pubKey: ""
    , pubKeyHash: PubKeyHash ""
    , assets: mempty
    }

mkInitialState :: WalletDetails -> Slot -> Minutes -> State
mkInitialState walletDetails currentSlot timezoneOffset =
  { walletDetails: walletDetails
  , menuOpen: false
  , screen: ContractsScreen
  , cards: mempty
  , currentSlot
  , timezoneOffset
  , templateState: Template.dummyState
  , contractsState: ContractHome.dummyState
  }

-- Some actions are handled in `MainFrame.State` because they involve
-- modifications of that state. See Note [State].
handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  ManageContract m =>
  ManageWallet m =>
  Toast m =>
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction ToggleMenu = modifying _menuOpen not

handleAction (SetScreen screen) =
  modify_
    $ set _menuOpen false
    <<< set _cards mempty
    <<< set _screen screen

handleAction (OpenCard card) = modifying _cards $ flip snoc card

handleAction CloseCard = do
  cards <- use _cards
  for_ (init cards) \remainingCards ->
    assign _cards remainingCards

handleAction (SetCurrentSlot currentSlot) = do
  toContractHome $ ContractHome.handleAction $ ContractHome.AdvanceTimedOutContracts currentSlot
  modify_
    $ set _currentSlot currentSlot

-- template actions that need to be handled here
handleAction (TemplateAction (Template.SetTemplate template)) = do
  mCurrentTemplate <- peruse (_templateState <<< _template)
  when (mCurrentTemplate /= Just template) $ assign _templateState $ Template.mkInitialState template
  handleAction $ SetScreen TemplateScreen

handleAction (TemplateAction Template.OpenTemplateLibraryCard) = handleAction $ OpenCard TemplateLibraryCard

handleAction (TemplateAction (Template.OpenCreateWalletCard tokenName)) = handleAction $ OpenCard $ CreateWalletCard $ Just tokenName

handleAction (TemplateAction Template.OpenSetupConfirmationCard) = handleAction $ OpenCard ContractSetupConfirmationCard

handleAction (TemplateAction Template.CloseSetupConfirmationCard) = do
  cards <- use _cards
  case lastOf traversed cards of
    Just ContractSetupConfirmationCard -> handleAction CloseCard
    _ -> pure unit

-- NOTE:  This handler makes works with the assumption than the contract was created from the template functionality
--        but that will only be the case for the person setting up the contract. Once we connect the backend, and a
--        contract is created by another participant, we won't be dealing with Extended contracts but actually
--        Semantic contracts and specially we won't have the roleWallets.
handleAction (TemplateAction Template.StartContract) = do
  templateState <- use _templateState
  currentSlot <- use _currentSlot
  let
    extendedContract = templateState ^. (_template <<< _extendedContract)

    templateContent = templateState ^. _templateContent

    metadata = templateState ^. (_template <<< _metaData)

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
    modifying (_contractsState <<< _contracts) (Map.insert contractId contractState)
    handleAction $ SetScreen $ ContractsScreen
    toContractHome $ ContractHome.handleAction $ ContractHome.OpenContract contractId

-- other template actions
handleAction (TemplateAction templateAction) = toTemplate $ Template.handleAction templateAction

-- contract home actions that need to be handled here
handleAction (ContractHomeAction (ContractHome.OpenTemplateLibraryCard)) = handleAction $ OpenCard TemplateLibraryCard

handleAction (ContractHomeAction a@(ContractHome.OpenContract _)) = do
  toContractHome $ ContractHome.handleAction a
  handleAction $ OpenCard ContractCard

-- other contract home actions
handleAction (ContractHomeAction contractAction) = void $ toContractHome $ ContractHome.handleAction contractAction

-- contract actions that need to be handled here
handleAction (ContractAction (Contract.AskConfirmation action)) = handleAction $ OpenCard $ ContractActionConfirmationCard action

handleAction (ContractAction (Contract.ConfirmAction action)) = do
  void $ toContract $ Contract.handleAction $ Contract.ConfirmAction action
  handleAction CloseCard

handleAction (ContractAction Contract.CancelConfirmation) = handleAction CloseCard

-- other contract  actions
handleAction (ContractAction contractAction) = void $ toContract $ Contract.handleAction contractAction

-- all other actions are handled in `MainFrame.State`
handleAction _ = pure unit

------------------------------------------------------------
toTemplate ::
  forall m msg slots.
  Functor m =>
  HalogenM Template.State Template.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toTemplate = mapSubmodule _templateState TemplateAction

toContractHome ::
  forall m msg slots.
  Functor m =>
  HalogenM ContractHome.State ContractHome.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toContractHome = mapSubmodule _contractsState ContractHomeAction

-- see note [dummyState]
toContract ::
  forall m msg slots.
  Functor m =>
  HalogenM Contract.State Contract.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toContract = mapMaybeSubmodule _selectedContract ContractAction Contract.dummyState
