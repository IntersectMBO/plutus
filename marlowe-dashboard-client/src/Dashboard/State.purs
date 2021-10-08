module Dashboard.State
  ( dummyState
  , mkInitialState
  , handleAction
  ) where

import Prologue
import Capability.Contract (class ManageContract)
import Capability.MainFrameLoop (class MainFrameLoop, callMainFrameAction)
import Capability.Marlowe (class ManageMarlowe, createContract, createPendingFollowerApp, followContract, followContractWithPendingFollowerApp, getFollowerApps, getRoleContracts, redeem, subscribeToPlutusApp)
import Capability.MarloweStorage (class ManageMarloweStorage, getWalletLibrary, insertIntoContractNicknames)
import Capability.Toast (class Toast, addToast)
import Clipboard (class MonadClipboard)
import Clipboard (handleAction) as Clipboard
import Contacts.Lenses (_assets, _cardSection, _pubKeyHash, _walletInfo, _walletLibrary, _walletNickname)
import Contacts.State (defaultWalletDetails, getAda)
import Contacts.State (handleAction, mkInitialState) as Contacts
import Contacts.Types (Action(..), State) as Contacts
import Contacts.Types (CardSection(..), WalletDetails, WalletLibrary)
import Contract.Lenses (_Started, _Starting, _marloweParams, _nickname, _selectedStep)
import Contract.State (applyTimeout)
import Contract.State (dummyState, handleAction, mkInitialState, mkPlaceholderState, updateState) as Contract
import Contract.Types (Action(..), State(..), StartingState) as Contract
import Control.Monad.Reader (class MonadAsk)
import Control.Monad.Reader.Class (ask)
import Dashboard.Lenses (_card, _cardOpen, _contractFilter, _contract, _contracts, _menuOpen, _selectedContract, _selectedContractFollowerAppId, _templateState, _walletCompanionStatus, _contactsState, _walletDetails)
import Dashboard.Types (Action(..), Card(..), ContractFilter(..), Input, State, WalletCompanionStatus(..))
import Data.Array (null)
import Data.Foldable (for_)
import Data.Lens (_Just, assign, elemOf, filtered, modifying, set, use, view, (^.))
import Data.Lens.At (at)
import Data.Lens.Extra (peruse)
import Data.Lens.Index (ix)
import Data.Lens.Traversal (traversed)
import Data.List (filter, fromFoldable) as List
import Data.Map (Map, delete, filterKeys, findMin, insert, lookup, mapMaybe, mapMaybeWithKey, toUnfoldable)
import Data.Maybe (fromMaybe)
import Data.Set (delete, fromFoldable, isEmpty) as Set
import Data.Time.Duration (Milliseconds(..))
import Data.Traversable (for)
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff)
import Env (DataProvider(..), Env)
import Halogen (HalogenM, modify_, query, tell)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import InputField.Lenses (_value)
import InputField.Types (Action(..)) as InputField
import LoadingSubmitButton.Types (Query(..), _submitButtonSlot)
import MainFrame.Types (Action(..)) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Client (ContractHistory, _chHistory, _chParams)
import Marlowe.Deinstantiate (findTemplate)
import Marlowe.Execution.State (getAllPayments)
import Marlowe.Extended.Metadata (_metaData)
import Marlowe.PAB (PlutusAppId, transactionFee)
import Marlowe.Semantics (MarloweData, MarloweParams, Party(..), Payee(..), Payment(..), Slot(..), _marloweContract)
import Template.Lenses (_contractNicknameInput, _contractSetupStage, _contractTemplate, _roleWalletInputs)
import Template.State (dummyState, handleAction, initialState) as Template
import Template.State (instantiateExtendedContract)
import Template.Types (Action(..), State) as Template
import Template.Types (ContractSetupStage(..))
import Toast.Types (ajaxErrorToast, decodedAjaxErrorToast, errorToast, successToast)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState mempty defaultWalletDetails mempty mempty (Slot zero)

{- [Workflow 2][4] Connect a wallet
When we connect a wallet, it has this initial state. Notable is the walletCompanionStatus of
`FirstUpdatePending`. Follow the trail of worflow comments to see what happens next.
-}
mkInitialState :: WalletLibrary -> WalletDetails -> Map PlutusAppId ContractHistory -> Map PlutusAppId String -> Slot -> State
mkInitialState walletLibrary walletDetails contracts contractNicknames currentSlot =
  let
    mkInitialContractState followerAppId contractHistory =
      let
        nickname = fromMaybe mempty $ lookup followerAppId contractNicknames
      in
        Contract.mkInitialState walletDetails currentSlot nickname contractHistory
  in
    { contactsState: Contacts.mkInitialState walletLibrary
    , walletDetails
    , walletCompanionStatus: FirstUpdatePending
    , menuOpen: false
    , card: Nothing
    , cardOpen: false
    , contracts: mapMaybeWithKey mkInitialContractState contracts
    , contractFilter: Running
    , selectedContractFollowerAppId: Nothing
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
{- [Workflow 3][0] Disconnect a wallet -}
handleAction _ DisconnectWallet = do
  walletLibrary <- use (_contactsState <<< _walletLibrary)
  walletDetails <- use _walletDetails
  contracts <- use _contracts
  callMainFrameAction $ MainFrame.EnterWelcomeState walletLibrary walletDetails contracts

handleAction _ (ContactsAction contactsAction) = case contactsAction of
  Contacts.CancelNewContactForRole -> assign _card $ Just ContractTemplateCard
  _ -> toContacts $ Contacts.handleAction contactsAction

handleAction _ ToggleMenu = modifying _menuOpen not

handleAction _ (ClipboardAction action) = do
  Clipboard.handleAction action
  addToast $ successToast "Copied to clipboard"

handleAction input (OpenCard card) = do
  -- first we set the card and reset the contact and template card states to their first section
  -- (we could check the card and only reset if relevant, but it doesn't seem worth the bother)
  modify_
    $ set _card (Just card)
    <<< set (_contactsState <<< _cardSection) Home
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
    assign (_contactsState <<< _walletLibrary) storedWalletLibrary
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

{- [Workflow 2][6] Connect a wallet
If we have just connected a wallet (and the walletCompanionStatus is still `FirstUpdatePending`),
then we know the `MarloweFollower` apps that are running in this wallet, and have just been given
the current state of its `WalletCompanion` app for the first time since connecting. If the status
of the `WalletCompanion` app contains a record of `MarloweParams` for any _new_ Marlowe contracts
(created since the last time we connected this wallet, and for which we therefore have no
corresponding `MarloweFollowr` apps), we now need to create `MarloweFollower` apps for those new
contracts.
In this case, we change the walletCompanionStatus to `LoadingNewContracts`, and subscribe to every
new `MarloweFollower`. We'll know the loading is finished when we've received the first status
update for each of these `MarloweFollower` apps through the WebSocket.
-}
{- [Workflow 4][2] Start a Marlowe contract
After starting a new Marlowe contract, we should receive a WebSocket notification informing us of
the `MarloweParams` and initial `MarloweData` for that contract (via a status update for our
`WalletCompanion` app). We now need to start following that contract with a `MarloweFollower` app.
If we started the contract ourselves, we already created a `MarloweFollower` app as a placeholder.
So here we need to check whether there is an existing `MarloweFollower` app with the right metadata
(and no `MarloweParams`) - and potentially use that instead of creating a new one.
If someone else started the contract, and gave us a role, we will have no placeholder
`MarloweFollower` app, and so we simply create a new one and start following immediately.
-}
handleAction input (UpdateFollowerApps companionAppState) = do
  walletCompanionStatus <- use _walletCompanionStatus
  walletDetails <- use _walletDetails
  existingContracts <- use _contracts
  let
    contractExists marloweParams =
      elemOf
        (traversed <<< _Started <<< _marloweParams)
        marloweParams
        existingContracts

    newContracts = filterKeys (not contractExists) companionAppState

    newContractsArray :: Array (Tuple MarloweParams MarloweData)
    newContractsArray = toUnfoldable newContracts
  if (walletCompanionStatus /= FirstUpdateComplete && (not $ null newContractsArray)) then
    assign _walletCompanionStatus $ LoadingNewContracts $ Set.fromFoldable $ map fst newContractsArray
  else
    assign _walletCompanionStatus FirstUpdateComplete
  void
    $ for newContractsArray \(marloweParams /\ marloweData) -> do
        let
          mTemplate = findTemplate $ view _marloweContract marloweData

          isStartingAndMetadataMatches :: Contract.State -> Maybe Contract.StartingState
          isStartingAndMetadataMatches = case _, mTemplate of
            Contract.Starting starting@{ metadata }, Just template
              | template.metaData == metadata -> Just starting
            _, _ -> Nothing

          mPendingContract = findMin $ mapMaybe isStartingAndMetadataMatches existingContracts
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
          MarlowePAB -> do
            ajaxFollowerApp <- case mPendingContract of
              Just { key: followerAppId } -> followContractWithPendingFollowerApp walletDetails marloweParams followerAppId
              Nothing -> followContract walletDetails marloweParams
            case ajaxFollowerApp of
              Left decodedAjaxError -> addToast $ decodedAjaxErrorToast "Failed to load new contract." decodedAjaxError
              Right (followerAppId /\ contractHistory) -> subscribeToPlutusApp followerAppId
          LocalStorage -> do
            ajaxFollowerApp <- followContract walletDetails marloweParams
            case ajaxFollowerApp of
              Left decodedAjaxError -> addToast $ decodedAjaxErrorToast "Failed to load new contract." decodedAjaxError
              Right (followerAppId /\ contractHistory) -> do
                handleAction input $ UpdateContract followerAppId contractHistory
                for_ mPendingContract \{ key, value } -> do
                  assign (_contracts <<< ix followerAppId <<< _Starting <<< _nickname) value.nickname
                  modifying _contracts $ delete key
                  insertIntoContractNicknames followerAppId value.nickname

{- [Workflow 2][8] Connect a wallet
If this is the first update we are receiving from a new `MarloweFollower` app that was created
after we connected the wallet, but _before_ the walletCompanionStatus was set to
`FirstUpdateComplete`, we need to remove the app from the `LoadingNewContracts` set. And if it's
the last element of that set, we can set the walletCompanionStatus to `FirstUpdateComplete`. This
(finally!) completes the workflow of connecting a wallet.
-}
{- [Workflow 4][4] Start a contract
If we started a contract (or someone else started one and gave us a role in it), we will have
created a `MarloweFollower` app for that contract, and started following the contract with that
`MarloweFollower` app. Since we will also be subscribed to that app, we will receive an update
about its initial state through the WebSocket. We potentially use that to change the corresponding
`Contract.State` from `Starting` to `Started`.
-}
{- [Workflow 5][2] Move a contract forward -}
handleAction input@{ currentSlot } (UpdateContract followerAppId contractHistory) =
  let
    chParams = view _chParams contractHistory
  in
    -- if the chParams have not yet been set, we can't do anything; that's fine though, we'll get
    -- another notification through the websocket as soon as they are set
    for_ chParams \(marloweParams /\ marloweData) -> do
      walletDetails <- use _walletDetails
      contracts <- use _contracts
      case lookup followerAppId contracts of
        Just contractState -> do
          let
            chHistory = view _chHistory contractHistory
          selectedStep <- peruse $ _selectedContract <<< _Started <<< _selectedStep
          modifying _contracts $ insert followerAppId $ Contract.updateState walletDetails marloweParams marloweData currentSlot chHistory contractState
          -- if the modification changed the currently selected step, that means the card for the contract
          -- that was changed is currently open, so we need to realign the step cards
          selectedStep' <- peruse $ _selectedContract <<< _Started <<< _selectedStep
          when (selectedStep /= selectedStep')
            $ for_ selectedStep' (handleAction input <<< ContractAction followerAppId <<< Contract.MoveToStep)
        Nothing -> for_ (Contract.mkInitialState walletDetails currentSlot mempty contractHistory) (modifying _contracts <<< insert followerAppId)
      -- if we're currently loading the first bunch of contracts, we can report that this one has now been loaded
      walletCompanionStatus <- use _walletCompanionStatus
      case walletCompanionStatus of
        LoadingNewContracts pendingMarloweParams -> do
          let
            updatedPendingMarloweParams = Set.delete marloweParams pendingMarloweParams
          if Set.isEmpty updatedPendingMarloweParams then
            assign _walletCompanionStatus FirstUpdateComplete
          else
            assign _walletCompanionStatus $ LoadingNewContracts updatedPendingMarloweParams
        _ -> pure unit

{- [Workflow 6][1] Redeem payments
This action is triggered every time we receive a status update for a `MarloweFollower` app. The
handler looks, in the corresponding contract, for any payments to roles for which the current
wallet holds the token, and then calls the "redeem" endpoint of the wallet's `MarloweApp` for each
one, to make sure those funds reach the user's wallet (without the user having to do anything).
This is not very sophisticated, and results in the "redeem" endpoint being called more times than
necessary (we are not attempting to keep track of which payments have already been redeemed). Also,
we thought it would be more user-friendly for now to trigger this automatically - but when we
integrate with real wallets, I'm pretty sure we will need to provide a UI for the user to do it
manually (and sign the transaction). So this will almost certainly have to change.
-}
handleAction input (RedeemPayments followerAppId) = do
  walletDetails <- use _walletDetails
  mStartedContract <- peruse $ _contracts <<< ix followerAppId <<< _Started
  for_ mStartedContract \{ executionState, marloweParams, userParties } ->
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
  selectedStep <- peruse $ _selectedContract <<< _Started <<< _selectedStep
  modifying
    ( _contracts
        <<< traversed
        <<< _Started
        <<< filtered
            ( \contract ->
                contract.executionState.mNextTimeout /= Nothing && contract.executionState.mNextTimeout <= Just currentSlot
            )
    )
    (applyTimeout currentSlot)
  selectedContractFollowerAppId <- use _selectedContractFollowerAppId
  for_ selectedContractFollowerAppId \followerAppId -> do
    -- If the modification changed the currently selected step, that means the screen for the
    -- contract that was changed is currently open, so we need to realign the step cards. We also
    -- call the CancelConfirmation action - because if the user had the action confirmation card
    -- open for an action in the current step, we want to close it (otherwise they could confirm an
    -- action that is no longer possible).
    selectedStep' <- peruse $ _selectedContract <<< _Started <<< _selectedStep
    when (selectedStep /= selectedStep') do
      for_ selectedStep' (handleAction input <<< ContractAction followerAppId <<< Contract.MoveToStep)
      handleAction input $ ContractAction followerAppId $ Contract.CancelConfirmation

handleAction input@{ currentSlot } (TemplateAction templateAction) = case templateAction of
  Template.OpenCreateWalletCard tokenName -> do
    modify_
      $ set _card (Just $ ContactsCard)
      <<< set (_contactsState <<< _cardSection) (NewWallet $ Just tokenName)
  {- [Workflow 4][0] Starting a Marlowe contract -}
  Template.StartContract -> do
    templateState <- use _templateState
    case instantiateExtendedContract currentSlot templateState of
      Nothing -> do
        void $ query _submitButtonSlot "action-pay-and-start" $ tell $ SubmitResult (Milliseconds 600.0) (Left "Error")
        addToast $ errorToast "Failed to instantiate contract." $ Just "Something went wrong when trying to instantiate a contract from this template using the parameters you specified."
      Just contract -> do
        -- the user enters wallet nicknames for roles; here we convert these into pubKeyHashes
        walletDetails <- use _walletDetails
        walletLibrary <- use (_contactsState <<< _walletLibrary)
        roleWalletInputs <- use (_templateState <<< _roleWalletInputs)
        let
          roleWallets = map (view _value) roleWalletInputs

          roles = mapMaybe (\walletNickname -> view (_walletInfo <<< _pubKeyHash) <$> lookup walletNickname walletLibrary) roleWallets
        ajaxCreateContract <- createContract walletDetails roles contract
        case ajaxCreateContract of
          -- TODO: make this error message more informative
          Left ajaxError -> do
            void $ query _submitButtonSlot "action-pay-and-start" $ tell $ SubmitResult (Milliseconds 600.0) (Left "Error")
            addToast $ ajaxErrorToast "Failed to initialise contract." ajaxError
          _ -> do
            -- Here we create a `MarloweFollower` app with no `MarloweParams`; when the next status
            -- update of the wallet's `WalletCompanion` app comes in, we will know the `MarloweParams`,
            -- and can use this placeholder `MarloweFollower` app to follow it. Follow the workflow
            -- comments to see more...
            ajaxPendingFollowerApp <- createPendingFollowerApp walletDetails
            case ajaxPendingFollowerApp of
              Left ajaxError -> do
                void $ query _submitButtonSlot "action-pay-and-start" $ tell $ SubmitResult (Milliseconds 600.0) (Left "Error")
                addToast $ ajaxErrorToast "Failed to initialise contract." ajaxError
              Right followerAppId -> do
                contractNickname <- use (_templateState <<< _contractNicknameInput <<< _value)
                insertIntoContractNicknames followerAppId contractNickname
                metaData <- use (_templateState <<< _contractTemplate <<< _metaData)
                modifying _contracts $ insert followerAppId $ Contract.mkPlaceholderState contractNickname metaData contract
                handleAction input CloseCard
                void $ query _submitButtonSlot "action-pay-and-start" $ tell $ SubmitResult (Milliseconds 600.0) (Right "")
                addToast $ successToast "The request to initialise this contract has been submitted."
                { dataProvider } <- ask
                when (dataProvider == LocalStorage) (handleAction input UpdateFromStorage)
                assign _templateState Template.initialState
  _ -> do
    walletLibrary <- use (_contactsState <<< _walletLibrary)
    toTemplate $ Template.handleAction { currentSlot, walletLibrary } templateAction

-- This action is a bridge from the Contacts to the Template modules. It is used to create a
-- contract for a specific role during contract setup.
handleAction input (SetContactForRole tokenName walletNickname) = do
  handleAction input $ TemplateAction Template.UpdateRoleWalletValidators
  handleAction input $ TemplateAction $ Template.RoleWalletInputAction tokenName $ InputField.SetValue walletNickname
  -- we assign the card directly rather than calling the OpenCard action, because this action is
  -- triggered when the ContactsCard is open, and we don't want to animate opening and closing
  -- cards - we just want to switch instantly back to this card
  assign _card $ Just ContractTemplateCard

handleAction input@{ currentSlot, tzOffset } (ContractAction followerAppId contractAction) = do
  walletDetails <- use _walletDetails
  startedState <- peruse $ _contracts <<< at followerAppId <<< _Just <<< _Started
  let
    contractInput = { currentSlot, walletDetails, followerAppId, tzOffset }
  case contractAction of
    Contract.AskConfirmation action ->
      for_ startedState \contractState ->
        handleAction input $ OpenCard
          $ ContractActionConfirmationCard
              followerAppId
              { action
              , contractState
              , currentSlot
              , transactionFeeQuote: transactionFee
              , userNickname: walletDetails ^. _walletNickname
              , walletBalance: getAda $ walletDetails ^. _assets
              }
    Contract.ConfirmAction action -> do
      void $ toContract followerAppId $ Contract.handleAction contractInput contractAction
      handleAction input CloseCard
    Contract.CancelConfirmation -> handleAction input CloseCard
    _ -> toContract followerAppId $ Contract.handleAction contractInput contractAction

------------------------------------------------------------
toContacts ::
  forall m msg slots.
  Functor m =>
  HalogenM Contacts.State Contacts.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toContacts = mapSubmodule _contactsState ContactsAction

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
