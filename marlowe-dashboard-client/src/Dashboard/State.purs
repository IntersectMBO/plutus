module Dashboard.State
  ( dummyState
  , mkInitialState
  , handleAction
  ) where

import Prelude
import Capability.Contract (class ManageContract)
import Capability.MainFrameLoop (class MainFrameLoop, callMainFrameAction)
import Capability.Marlowe (class ManageMarlowe, createContract, createPendingFollowerApp, followContract, followContractWithPendingFollowerApp, getFollowerApps, getRoleContracts, redeem, subscribeToPlutusApp)
import Capability.MarloweStorage (class ManageMarloweStorage, getWalletLibrary, insertIntoContractNicknames)
import Capability.Toast (class Toast, addToast)
import Clipboard (class MonadClipboard)
import Contract.Lenses (_mMarloweParams, _nickname, _selectedStep)
import Contract.State (applyTimeout)
import Contract.State (dummyState, handleAction, mkInitialState, mkPlaceholderState, updateState) as Contract
import Contract.Types (Action(..), State) as Contract
import Control.Monad.Reader (class MonadAsk)
import Control.Monad.Reader.Class (ask)
import Dashboard.Lenses (_card, _cardOpen, _contractFilter, _contract, _contracts, _menuOpen, _selectedContract, _selectedContractFollowerAppId, _templateState, _walletDataState, _walletDetails)
import Dashboard.Types (Action(..), Card(..), ContractFilter(..), Input, State)
import Data.Array (elem)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, filtered, modifying, over, set, use, view)
import Data.Lens.Extra (peruse)
import Data.Lens.Traversal (traversed)
import Data.List (filter, fromFoldable) as List
import Data.Map (Map, alter, delete, filter, filterKeys, findMin, insert, lookup, mapMaybe, mapMaybeWithKey, toUnfoldable, values)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Time.Duration (Minutes(..))
import Data.Traversable (for)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff)
import Env (DataProvider(..), Env)
import Halogen (HalogenM, modify_)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import InputField.Lenses (_value)
import InputField.Types (Action(..)) as InputField
import MainFrame.Types (Action(..)) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Deinstantiate (findTemplate)
import Marlowe.Execution.State (getAllPayments)
import Marlowe.Extended.Metadata (_metaData)
import Marlowe.PAB (ContractHistory, MarloweData, MarloweParams, PlutusAppId)
import Marlowe.Semantics (Party(..), Payee(..), Payment(..), Slot(..))
import Template.Lenses (_contractNicknameInput, _contractSetupStage, _contractTemplate, _roleWalletInputs)
import Template.State (dummyState, handleAction, initialState) as Template
import Template.State (instantiateExtendedContract)
import Template.Types (Action(..), State) as Template
import Template.Types (ContractSetupStage(..))
import Toast.Types (ajaxErrorToast, decodedAjaxErrorToast, errorToast, successToast)
import WalletData.Lenses (_cardSection, _pubKeyHash, _walletInfo, _walletLibrary, _walletNickname)
import WalletData.State (defaultWalletDetails)
import WalletData.State (handleAction, mkInitialState) as WalletData
import WalletData.Types (Action(..), State) as WalletData
import WalletData.Types (CardSection(..), WalletDetails, WalletLibrary)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState mempty defaultWalletDetails mempty mempty (Slot zero) (Minutes zero)

mkInitialState :: WalletLibrary -> WalletDetails -> Map PlutusAppId ContractHistory -> Map PlutusAppId String -> Slot -> Minutes -> State
mkInitialState walletLibrary walletDetails contracts contractNicknames currentSlot timezoneOffset =
  let
    mkInitialContractState followerAppId contractHistory =
      let
        nickname = fromMaybe mempty $ lookup followerAppId contractNicknames
      in
        Contract.mkInitialState walletDetails currentSlot nickname contractHistory
  in
    { walletDataState: WalletData.mkInitialState walletLibrary
    , walletDetails
    , menuOpen: false
    , card: Nothing
    , cardOpen: false
    , contracts: mapMaybeWithKey mkInitialContractState contracts
    , contractFilter: Running
    , selectedContractFollowerAppId: Nothing
    , timezoneOffset
    , templateState: Template.dummyState
    }

handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  MainFrameLoop m =>
  ManageContract m =>
  ManageMarloweStorage m =>
  ManageMarlowe m =>
  Toast m =>
  MonadClipboard m =>
  Input -> Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction _ PutdownWallet = do
  walletLibrary <- use (_walletDataState <<< _walletLibrary)
  walletDetails <- use _walletDetails
  contracts <- use _contracts
  callMainFrameAction $ MainFrame.EnterWelcomeState walletLibrary walletDetails contracts

handleAction _ (WalletDataAction walletDataAction) = case walletDataAction of
  WalletData.CancelNewContactForRole -> assign _card $ Just ContractTemplateCard
  _ -> toWalletData $ WalletData.handleAction walletDataAction

handleAction _ ToggleMenu = modifying _menuOpen not

handleAction input (OpenCard card) = do
  -- first we set the card and reset the contact and template card states to their first section
  -- (we could check the card and only reset if relevant, but it doesn't seem worth the bother)
  modify_
    $ set _card (Just card)
    <<< set (_walletDataState <<< _cardSection) Home
    <<< set (_templateState <<< _contractSetupStage) Start
  -- then we set the card to open (and close the mobile menu) in a separate `modify_`, so that the
  -- CSS transition animation works
  modify_
    $ set _cardOpen true
    <<< set _menuOpen false

handleAction _ CloseCard = assign _cardOpen false

handleAction _ (SetContractFilter contractFilter) = assign _contractFilter contractFilter

handleAction input (SelectContract mFollowerAppId) = assign _selectedContractFollowerAppId mFollowerAppId

-- Until everything is working in the PAB, we are simulating persistent and shared data using localStorage; this
-- action updates the state to match the localStorage, and should be called whenever the stored data changes.
-- It's not very subtle or efficient - it just updates everything in one go.
handleAction input@{ currentSlot } UpdateFromStorage = do
  { dataProvider } <- ask
  when (dataProvider == LocalStorage) do
    walletDetails <- use _walletDetails
    -- update the wallet library
    storedWalletLibrary <- getWalletLibrary
    assign (_walletDataState <<< _walletLibrary) storedWalletLibrary
    -- update the current wallet details to match those from the wallet library
    let
      mStoredWalletDetails = lookup (view _walletNickname walletDetails) storedWalletLibrary
    for_ mStoredWalletDetails \storedWalletDetails -> assign _walletDetails storedWalletDetails
    -- make sure we have contracts for all the follower apps
    updatedWalletDetails <- use _walletDetails
    ajaxCompanionAppState <- getRoleContracts updatedWalletDetails
    for_ ajaxCompanionAppState (handleAction input <<< UpdateFollowerApps)
    -- make sure all contracts are in sync with their follower apps
    ajaxFollowerApps <- getFollowerApps walletDetails
    for_ ajaxFollowerApps \followerApps ->
      let
        unfoldedFollowerApps :: Array (Tuple PlutusAppId ContractHistory)
        unfoldedFollowerApps = toUnfoldable followerApps
      in
        void $ for unfoldedFollowerApps \(plutusAppId /\ contractHistory) -> handleAction input $ UpdateContract plutusAppId contractHistory

-- this handler takes the wallet companion app state (which contains MarloweParams of all the contracts)
-- the wallet is interested in, compares it to the existing contracts, and either creates new follower
-- apps or activates pending ones for any contracts that aren't yet being followed
handleAction input (UpdateFollowerApps companionAppState) = do
  walletDetails <- use _walletDetails
  existingContracts <- use _contracts
  let
    contractExists marloweParams = elem (Just marloweParams) (view _mMarloweParams <$> values existingContracts)

    newContracts = filterKeys (not contractExists) companionAppState

    newContractsArray :: Array (Tuple MarloweParams MarloweData)
    newContractsArray = toUnfoldable newContracts
  void
    $ for newContractsArray \(marloweParams /\ marloweData) -> do
        let
          mTemplate = findTemplate marloweData.marloweContract

          hasRightMetaData :: Contract.State -> Boolean
          hasRightMetaData { mMarloweParams, metadata } = case mMarloweParams, mTemplate of
            Nothing, Just template -> template.metaData == metadata
            _, _ -> false

          mPendingContract = findMin $ filter hasRightMetaData existingContracts
        -- Note [PendingContracts]: Okay, here's the problem: When we're using the PAB, and a contract is created,
        -- we create a follower app immediately as a placeholder (and remember its PlutusAppId), then we wait for
        -- the wallet companion app to tell us the MarloweParams of the contract we created, and pass those to the
        -- pending follower app. Fine. But when we're using the LocalStorage as our dataProvider, this workflow
        -- doesn't quite work. This is because the LocalStorage doesn't keep a record of PlutusAppIds, but just
        -- derives them as a function of the MarloweParams (see note [MarloweParams] in Capability.Marlowe). So
        -- when we create a pending follower app with LocalStorage, we get back what is ultimately the wrong
        -- PlutusAppId (and we can't know the right one until we've generated the MarloweParams). At that point we
        -- could try to update the PlutusAppId, but it's simpler to just delete the pending follower app and
        -- create a new one with the right ID (and the right key in the contracts map).
        --
        -- This solution is ugly for two reasons: (1) In general, the Marlowe capability should be the only thing
        -- that cares about the dataProvider and does things differently depending on what it is. (2) In particular,
        -- what we're doing here means that the LocalStorage implementations of `createPendingFollowerApp` and
        -- `followContractWithPendingFollowerApp` are completely pointless (the first one is called at the
        -- appropriate point, but here we just delete the pending follower app that it created without making any
        -- use of it; and the second is never even called).
        --
        -- (Note: There are sensible LocalStorage implementations of these useless functions in the Marlowe capability.
        -- Why? Because I wrote them before I realised that the simplest solution to the present problem would be to
        -- stop using them. I might as well leave them there in case they become useful again at some point.)
        --
        -- But the good news is that all of this is for the bin anyway, as soon as the PAB is working fully and we can
        -- get rid of the LocalStorage hack altogether. So I think in the meantime this will do (and I don't want to
        -- waste any more time than I already have on trying to do something nicer).
        { dataProvider } <- ask
        case dataProvider of
          LocalStorage -> do
            ajaxFollowerApp <- followContract walletDetails marloweParams
            case ajaxFollowerApp of
              Left decodedAjaxError -> addToast $ decodedAjaxErrorToast "Failed to load new contract." decodedAjaxError
              Right (followerAppId /\ contractHistory) -> do
                handleAction input $ UpdateContract followerAppId contractHistory
                for_ mPendingContract \{ key, value } -> do
                  modifying _contracts
                    $ delete key
                    <<< alter (map $ set _nickname value.nickname) followerAppId
                  insertIntoContractNicknames followerAppId value.nickname
          PAB _ -> do
            ajaxFollowerApp <- case mPendingContract of
              Just { key: followerAppId } -> followContractWithPendingFollowerApp walletDetails marloweParams followerAppId
              Nothing -> followContract walletDetails marloweParams
            case ajaxFollowerApp of
              Left decodedAjaxError -> addToast $ decodedAjaxErrorToast "Failed to load new contract." decodedAjaxError
              Right (followerAppId /\ contractHistory) -> subscribeToPlutusApp dataProvider followerAppId

-- this handler updates the state of an individual contract
handleAction input@{ currentSlot } (UpdateContract followerAppId contractHistory@{ chParams, chHistory }) =
  -- if the chParams have not yet been set, we can't do anything; that's fine though, we'll get
  -- another notification through the websocket as soon as they are set
  for_ chParams \(marloweParams /\ marloweData) -> do
    walletDetails <- use _walletDetails
    contracts <- use _contracts
    case lookup followerAppId contracts of
      Just contractState -> do
        selectedStep <- peruse $ _selectedContract <<< _selectedStep
        modifying _contracts $ insert followerAppId $ Contract.updateState walletDetails marloweParams currentSlot chHistory contractState
        -- if the modification changed the currently selected step, that means the card for the contract
        -- that was changed is currently open, so we need to realign the step cards
        selectedStep' <- peruse $ _selectedContract <<< _selectedStep
        when (selectedStep /= selectedStep')
          $ for_ selectedStep' (handleAction input <<< ContractAction followerAppId <<< Contract.MoveToStep)
      Nothing -> for_ (Contract.mkInitialState walletDetails currentSlot mempty contractHistory) (modifying _contracts <<< insert followerAppId)

-- This handler looks, in the given contract, for any payments to roles for which the current
-- wallet holds the token, and then calls the "redeem" endpoint of the main marlowe app for each
-- one, to make sure those funds reach the user's wallet (without the user having to do anything).
-- The handler is called every time we receive a notification that the state of the contract's
-- follower app has changed, so it will be called more often that is necessary. But there is no way
-- to guard against that. (Well, we could keep track of payments redeemed in the application state,
-- but that record would be lost when the browser is closed - and then those payments would all be
-- redeemed again anyway the next time the user picks up the wallet. Since these duplicate requests
-- will happen anyway, therefore, this extra complication doesn't seem worth the bother.
handleAction input (RedeemPayments followerAppId) = do
  walletDetails <- use _walletDetails
  contracts <- use _contracts
  for_ (lookup followerAppId contracts) \{ executionState, mMarloweParams, userParties } ->
    for_ mMarloweParams \marloweParams ->
      let
        payments = getAllPayments executionState

        isToParty party (Payment _ payee _) = case payee of
          Party p -> p == party
          _ -> false
      in
        for (List.fromFoldable userParties) \party ->
          let
            paymentsToParty = List.filter (isToParty party) payments
          in
            for paymentsToParty \payment -> case payment of
              Payment _ (Party (Role tokenName)) _ -> void $ redeem walletDetails marloweParams tokenName
              _ -> pure unit

handleAction input@{ currentSlot } AdvanceTimedoutSteps = do
  walletDetails <- use _walletDetails
  selectedStep <- peruse $ _selectedContract <<< _selectedStep
  modify_
    $ over
        (_contracts <<< traversed <<< filtered (\contract -> contract.executionState.mNextTimeout /= Nothing && contract.executionState.mNextTimeout <= Just currentSlot))
        (applyTimeout currentSlot)
  selectedContractFollowerAppId <- use _selectedContractFollowerAppId
  for_ selectedContractFollowerAppId \followerAppId -> do
    -- If the modification changed the currently selected step, that means the screen for the
    -- contract that was changed is currently open, so we need to realign the step cards. We also
    -- call the CancelConfirmation action - because if the user had the action confirmation card
    -- open for an action in the current step, we want to close it (otherwise they could confirm an
    -- action that is no longer possible).
    selectedStep' <- peruse $ _selectedContract <<< _selectedStep
    when (selectedStep /= selectedStep') do
      for_ selectedStep' (handleAction input <<< ContractAction followerAppId <<< Contract.MoveToStep)
      handleAction input $ ContractAction followerAppId $ Contract.CancelConfirmation

handleAction input@{ currentSlot } (TemplateAction templateAction) = case templateAction of
  Template.OpenCreateWalletCard tokenName -> do
    modify_
      $ set _card (Just $ WalletDataCard)
      <<< set (_walletDataState <<< _cardSection) (NewWallet $ Just tokenName)
  Template.StartContract -> do
    templateState <- use _templateState
    case instantiateExtendedContract currentSlot templateState of
      Nothing -> addToast $ errorToast "Failed to instantiate contract." $ Just "Something went wrong when trying to instantiate a contract from this template using the parameters you specified."
      Just contract -> do
        -- the user enters wallet nicknames for roles; here we convert these into pubKeyHashes
        walletDetails <- use _walletDetails
        walletLibrary <- use (_walletDataState <<< _walletLibrary)
        roleWalletInputs <- use (_templateState <<< _roleWalletInputs)
        let
          roleWallets = map (view _value) roleWalletInputs

          roles = mapMaybe (\walletNickname -> view (_walletInfo <<< _pubKeyHash) <$> lookup walletNickname walletLibrary) roleWallets
        ajaxCreateContract <- createContract walletDetails roles contract
        case ajaxCreateContract of
          -- TODO: make this error message more informative
          Left ajaxError -> addToast $ ajaxErrorToast "Failed to initialise contract." ajaxError
          _ -> do
            -- We create a follower app now with no MarloweParams; when the next notification of a new contract
            -- notification comes in, a follower app with no MarloweParams but the right metadata will be used.
            ajaxPendingFollowerApp <- createPendingFollowerApp walletDetails
            case ajaxPendingFollowerApp of
              Left ajaxError -> addToast $ ajaxErrorToast "Failed to initialise contract." ajaxError
              Right followerAppId -> do
                contractNickname <- use (_templateState <<< _contractNicknameInput <<< _value)
                insertIntoContractNicknames followerAppId contractNickname
                metaData <- use (_templateState <<< _contractTemplate <<< _metaData)
                modifying _contracts $ insert followerAppId $ Contract.mkPlaceholderState contractNickname metaData contract
                handleAction input CloseCard
                addToast $ successToast "The request to initialise this contract has been submitted."
                { dataProvider } <- ask
                when (dataProvider == LocalStorage) (handleAction input UpdateFromStorage)
                assign _templateState Template.initialState
  _ -> do
    walletLibrary <- use (_walletDataState <<< _walletLibrary)
    toTemplate $ Template.handleAction { currentSlot, walletLibrary } templateAction

-- This action is a bridge from the WalletData to the Template modules. It is used to create a
-- contract for a specific role during contract setup.
handleAction input (SetContactForRole tokenName walletNickname) = do
  handleAction input $ TemplateAction Template.UpdateRoleWalletValidators
  handleAction input $ TemplateAction $ Template.RoleWalletInputAction tokenName $ InputField.SetValue walletNickname
  -- we assign the card directly rather than calling the OpenCard action, because this action is
  -- triggered when the WalletDataCard is open, and we don't want to animate opening and closing
  -- cards - we just want to switch instantly back to this card
  assign _card $ Just ContractTemplateCard

handleAction input@{ currentSlot } (ContractAction followerAppId contractAction) = do
  walletDetails <- use _walletDetails
  let
    contractInput = { currentSlot, walletDetails, followerAppId }
  case contractAction of
    Contract.AskConfirmation action -> handleAction input $ OpenCard $ ContractActionConfirmationCard followerAppId action
    Contract.ConfirmAction action -> do
      void $ toContract followerAppId $ Contract.handleAction contractInput contractAction
      handleAction input CloseCard
    Contract.CancelConfirmation -> handleAction input CloseCard
    _ -> toContract followerAppId $ Contract.handleAction contractInput contractAction

------------------------------------------------------------
toWalletData ::
  forall m msg slots.
  Functor m =>
  HalogenM WalletData.State WalletData.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toWalletData = mapSubmodule _walletDataState WalletDataAction

toTemplate ::
  forall m msg slots.
  Functor m =>
  HalogenM Template.State Template.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toTemplate = mapSubmodule _templateState TemplateAction

-- see note [dummyState] in MainFrame.State
toContract ::
  forall m msg slots.
  Functor m =>
  PlutusAppId ->
  HalogenM Contract.State Contract.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toContract followerAppId = mapMaybeSubmodule (_contract followerAppId) (ContractAction followerAppId) Contract.dummyState
