module Welcome.State
  ( dummyState
  , mkInitialState
  , handleAction
  ) where

import Prologue
import Capability.MainFrameLoop (class MainFrameLoop, callMainFrameAction)
import Capability.Marlowe (class ManageMarlowe, createWallet, lookupWalletDetails)
import Capability.MarloweStorage (class ManageMarloweStorage, clearAllLocalStorage, insertIntoWalletLibrary)
import Capability.Toast (class Toast, addToast)
import Clipboard (class MonadClipboard)
import Clipboard (handleAction) as Clipboard
import Control.Monad.Reader (class MonadAsk)
import Data.Foldable (for_)
import Data.Lens (assign, modifying, set, use, view, (^.))
import Data.Map (filter, findMin, insert, lookup)
import Data.Newtype (unwrap)
import Data.UUID (emptyUUID, toString) as UUID
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM, liftEffect, modify_)
import Halogen.Extra (mapSubmodule)
import Halogen.Query.HalogenM (mapAction)
import InputField.State (handleAction, mkInitialState) as InputField
import InputField.Types (Action(..), State) as InputField
import MainFrame.Types (Action(..)) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.PAB (PlutusAppId(..))
import Network.RemoteData (RemoteData(..), fromEither)
import Toast.Types (ajaxErrorToast, errorToast, successToast)
import Types (WebData)
import Contacts.Lenses (_companionAppId, _walletNickname)
import Contacts.State (parsePlutusAppId, walletNicknameError)
import Contacts.Types (WalletDetails, WalletIdError, WalletLibrary, WalletNicknameError)
import Web.HTML (window)
import Web.HTML.Location (reload)
import Web.HTML.Window (location)
import Welcome.Lenses (_card, _cardOpen, _enteringDashboardState, _remoteWalletDetails, _walletId, _walletLibrary, _walletNicknameInput, _walletNicknameOrIdInput)
import Welcome.Types (Action(..), Card(..), State, WalletNicknameOrIdError(..))

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState mempty

mkInitialState :: WalletLibrary -> State
mkInitialState walletLibrary =
  { walletLibrary
  , card: Nothing
  , cardOpen: false
  , walletNicknameOrIdInput: InputField.mkInitialState Nothing
  , walletNicknameInput: InputField.mkInitialState Nothing
  , walletId: PlutusAppId UUID.emptyUUID
  , remoteWalletDetails: NotAsked
  , enteringDashboardState: false
  }

-- Some actions are handled in `MainFrame.State` because they involve
-- modifications of that state. See Note [State] in MainFrame.State.
handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  MainFrameLoop m =>
  ManageMarlowe m =>
  ManageMarloweStorage m =>
  Toast m =>
  MonadClipboard m =>
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction (OpenCard card) =
  modify_
    $ set _card (Just card)
    <<< set _cardOpen true

handleAction CloseCard = do
  modify_
    $ set _remoteWalletDetails NotAsked
    <<< set _enteringDashboardState false
    <<< set _cardOpen false
    <<< set _walletId dummyState.walletId
  handleAction $ WalletNicknameOrIdInputAction $ InputField.Reset
  handleAction $ WalletNicknameInputAction $ InputField.Reset

{- [Workflow 1][0] Generating a new wallet
Here we attempt to create a new demo wallet (with everything that entails), and - if successful -
open up the UseNewWalletCard for connecting the wallet just created.
Note the `createWallet` function doesn't just create a wallet. It also creates two PAB apps for
that wallet: a `WalletCompanion` and a `MarloweApp`.
- The `WalletCompanion` will watch for any new role tokens paid to this wallet, and then update its
  internal state to include the `MarloweParams` and initial `MarloweData` for the corresponding
  contract.
- The `MarloweApp` is a control app, used to create Marlowe contracts, apply inputs, and redeem
  payments to this wallet.
-}
handleAction GenerateWallet = do
  walletLibrary <- use _walletLibrary
  assign _remoteWalletDetails Loading
  ajaxWalletDetails <- createWallet
  assign _remoteWalletDetails $ fromEither ajaxWalletDetails
  case ajaxWalletDetails of
    Left ajaxError -> addToast $ ajaxErrorToast "Failed to generate wallet." ajaxError
    Right walletDetails -> do
      handleAction $ WalletNicknameInputAction $ InputField.Reset
      handleAction $ WalletNicknameInputAction $ InputField.SetValidator $ walletNicknameError walletLibrary
      assign _walletId $ walletDetails ^. _companionAppId
      handleAction $ OpenCard UseNewWalletCard

{- [Workflow 2][0] Connect a wallet
The app lets you connect a wallet using an "omnibox" input, into which you can either enter a
wallet nickname that you have saved in your browser's LocalStorage, or the appId of the wallet's
`WalletCompanion` app. If you enter a valid appId, we lookup the details of a corresponding wallet
in the PAB; if you enter a nickname, we have a cache of the details in LocalStorage. Either way,
we then open up the UseWalletCard (or UseNewWalletCard), essentially a confirmation box for
connecting this wallet.
TODO: We currently use the appId of the wallet's `WalletCompanion` app as the "public" identifier
for wallets: this is what is shown to the user, what they are told to copy and give to others, and
what they need to enter into the "omnibox". This is because we need to know several things about
each wallet (see the `WalletDetails` type), and in the initial stages of this app's development,
it was possible to find out all of these things from just the appId of the `WalletCompanion`, and
not possible to find out all of them from anything else.
However, I realised recently that - with some PAB developments that have happened since, it should
now be possible to determine the full `WalletDetails` given only the ID of the wallet itself. This
might be preferable. The general strategy would be this: (1) use `Capability.Wallet.getWalletInfo`
to get the wallet's pubKey and pubKeyHash; (2) use `Capability.Contract.getWalletContractInstances`
to get all the contracts (i.e. PAB apps) running in that wallet; (3) search those apps for the
wallet's `WalletCompanion` and `MarloweApp` (by checking their `cicDefinition`).
-}
handleAction (WalletNicknameOrIdInputAction inputFieldAction) = do
  toWalletNicknameOrIdInput $ InputField.handleAction inputFieldAction
  case inputFieldAction of
    InputField.SetValue walletNicknameOrId -> do
      handleAction $ WalletNicknameOrIdInputAction $ InputField.SetValidator $ const Nothing
      assign _remoteWalletDetails NotAsked
      for_ (parsePlutusAppId walletNicknameOrId) \plutusAppId -> do
        assign _remoteWalletDetails Loading
        handleAction $ WalletNicknameOrIdInputAction $ InputField.SetValidator $ walletNicknameOrIdError Loading
        ajaxWalletDetails <- lookupWalletDetails plutusAppId
        assign _remoteWalletDetails $ fromEither ajaxWalletDetails
        handleAction $ WalletNicknameOrIdInputAction $ InputField.SetValidator $ walletNicknameOrIdError $ fromEither ajaxWalletDetails
        case ajaxWalletDetails of
          Left ajaxError -> pure unit -- feedback is shown in the view in this case
          Right walletDetails -> do
            -- check whether this wallet ID is already in the walletLibrary ...
            walletLibrary <- use _walletLibrary
            assign _walletId plutusAppId
            case findMin $ filter (\w -> w ^. _companionAppId == plutusAppId) walletLibrary of
              Just { key, value } -> do
                -- if so, open the UseWalletCard
                handleAction $ WalletNicknameInputAction $ InputField.SetValue key
                handleAction $ OpenCard UseWalletCard
              Nothing -> do
                -- otherwise open the UseNewWalletCard
                handleAction $ WalletNicknameInputAction $ InputField.Reset
                handleAction $ WalletNicknameInputAction $ InputField.SetValidator $ walletNicknameError walletLibrary
                handleAction $ OpenCard UseNewWalletCard
    InputField.SetValueFromDropdown walletNicknameOrId -> do
      -- in this case we know it's a wallet nickname, and we want to open the use card
      -- for the corresponding wallet
      walletLibrary <- use _walletLibrary
      for_ (lookup walletNicknameOrId walletLibrary) (handleAction <<< OpenUseWalletCardWithDetails)
    _ -> pure unit

{- [Workflow 2][1] Connect a wallet
If we are connecting a wallet that was selected by the user inputting a wallet nickname, then we
will have a cache of it's `WalletDetails` in LocalStorage. But those details may well be out of
date. This intermediate step makes sure we have the current details before proceeding.
This is also factored out into a separate handler so that it can be called directly when the user
selects a wallet nickname from the dropdown menu (as well as indirectly via the previous handler).
-}
handleAction (OpenUseWalletCardWithDetails walletDetails) = do
  assign _remoteWalletDetails Loading
  ajaxWalletDetails <- lookupWalletDetails $ view _companionAppId walletDetails
  assign _remoteWalletDetails $ fromEither ajaxWalletDetails
  case ajaxWalletDetails of
    Left ajaxError -> handleAction $ OpenCard LocalWalletMissingCard
    Right _ -> do
      handleAction $ WalletNicknameOrIdInputAction $ InputField.Reset
      handleAction $ WalletNicknameInputAction $ InputField.SetValue $ view _walletNickname walletDetails
      assign _walletId $ walletDetails ^. _companionAppId
      handleAction $ OpenCard UseWalletCard

handleAction (WalletNicknameInputAction inputFieldAction) = toWalletNicknameInput $ InputField.handleAction inputFieldAction

{- [Workflow 2][2] Connect a wallet
This action is triggered by clicking the confirmation button on the UseWalletCard or
UseNewWalletCard. It saves the wallet nickname to LocalStorage, and then calls the
`MainFrame.EnterDashboardState` action.
-}
handleAction (ConnectWallet walletNickname) = do
  assign _enteringDashboardState true
  remoteWalletDetails <- use _remoteWalletDetails
  case remoteWalletDetails of
    Success walletDetails -> do
      let
        walletDetailsWithNickname = set _walletNickname walletNickname walletDetails
      modifying _walletLibrary (insert walletNickname walletDetailsWithNickname)
      insertIntoWalletLibrary walletDetailsWithNickname
      walletLibrary <- use _walletLibrary
      callMainFrameAction $ MainFrame.EnterDashboardState walletLibrary walletDetailsWithNickname
    _ -> do
      -- this should never happen (the button to use a wallet should be disabled unless
      -- remoteWalletDetails is Success), but let's add some sensible behaviour anyway just in case
      handleAction CloseCard
      addToast $ errorToast "Unable to use this wallet." $ Just "Details for this wallet could not be loaded."

handleAction ClearLocalStorage = do
  clearAllLocalStorage
  liftEffect do
    location_ <- location =<< window
    reload location_

handleAction (ClipboardAction clipboardAction) = do
  mapAction ClipboardAction $ Clipboard.handleAction clipboardAction
  addToast $ successToast "Copied to clipboard"

------------------------------------------------------------
toWalletNicknameOrIdInput ::
  forall m msg slots.
  Functor m =>
  HalogenM (InputField.State WalletNicknameOrIdError) (InputField.Action WalletNicknameOrIdError) slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toWalletNicknameOrIdInput = mapSubmodule _walletNicknameOrIdInput WalletNicknameOrIdInputAction

toWalletNicknameInput ::
  forall m msg slots.
  Functor m =>
  HalogenM (InputField.State WalletNicknameError) (InputField.Action WalletNicknameError) slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toWalletNicknameInput = mapSubmodule _walletNicknameInput WalletNicknameInputAction

------------------------------------------------------------
walletNicknameOrIdError :: WebData WalletDetails -> String -> Maybe WalletNicknameOrIdError
walletNicknameOrIdError remoteWalletDetails _ = case remoteWalletDetails of
  Loading -> Just UnconfirmedWalletNicknameOrId
  Failure _ -> Just NonexistentWalletNicknameOrId
  _ -> Nothing
