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
import Contacts.Lenses (_companionAppId)
import Contacts.State (parsePlutusAppId, walletNicknameError)
import Contacts.Types (WalletDetails, WalletLibrary, WalletNicknameError)
import Control.Monad.Reader (class MonadAsk)
import Data.Foldable (for_)
import Data.Lens (_1, _2, _Just, assign, modifying, prism', set, use, view, (^.))
import Data.Lens.Extra (peruse)
import Data.Lens.Index (ix)
import Data.Map (filter, findMin, insert)
import Data.Traversable (traverse_)
import Data.Tuple (uncurry)
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM, liftEffect, modify_)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import Halogen.Query.HalogenM (mapAction)
import InputField.State (dummyState, handleAction) as InputField
import InputField.Types (Action(..), State) as InputField
import MainFrame.Types (Action(..)) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Network.RemoteData (RemoteData(..), fromEither)
import Toast.Types (ajaxErrorToast, successToast)
import Types (WebData)
import Web.HTML (window)
import Web.HTML.Location (reload)
import Web.HTML.Window (location)
import Welcome.Lenses (_enteringDashboardState, _modal, _remoteWalletDetails, _walletLibrary, _walletNicknameOrIdInput)
import Welcome.Types (Action(..), Modal(..), State, WalletNicknameOrIdError(..))

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState mempty

mkInitialState :: WalletLibrary -> State
mkInitialState walletLibrary =
  { walletLibrary
  , modal: Nothing
  , walletNicknameOrIdInput: InputField.dummyState
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
handleAction (OpenModal card) =
  modify_
    $ set _modal (Just $ Tuple card true)

handleAction CloseModal = do
  modify_
    $ set _remoteWalletDetails NotAsked
    <<< set _enteringDashboardState false
    <<< set (_modal <<< _Just <<< _2) false
  handleAction $ WalletNicknameOrIdInputAction $ InputField.Reset

{- [Workflow 1][0] Generating a new wallet
Here we attempt to create a new demo wallet (with everything that entails), and - if successful -
open up the UseNewWallet modal for connecting the wallet just created.
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
    Right { companionAppId } -> openModal $ UseNewWallet (initialNicknameInputState walletLibrary) companionAppId

{- [Workflow 2][0] Connect a wallet
The app lets you connect a wallet using an "omnibox" input, into which you can either enter a
wallet nickname that you have saved in your browser's LocalStorage, or the appId of the wallet's
`WalletCompanion` app. If you enter a valid appId, we lookup the details of a corresponding wallet
in the PAB; if you enter a nickname, we have a cache of the details in LocalStorage. Either way,
we then open up the UseWallet (or UseNewWallet) modal, essentially a confirmation box for
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
            case findMin $ filter (\w -> w ^. _companionAppId == plutusAppId) walletLibrary of
              -- if so, open the UseWallet modal
              Just { key, value } -> openModal $ UseWallet key plutusAppId
              -- otherwise open the UseNewWallet modal
              Nothing -> openModal $ UseNewWallet (initialNicknameInputState walletLibrary) plutusAppId
    InputField.SetValueFromDropdown walletNicknameOrId -> do
      -- in this case we know it's a wallet nickname, and we want to open the use card
      -- for the corresponding wallet
      wallet <- peruse $ _walletLibrary <<< ix walletNicknameOrId
      traverse_ (handleAction <<< OpenUseWalletModalWithDetails) wallet
    _ -> pure unit

{- [Workflow 2][1] Connect a wallet
If we are connecting a wallet that was selected by the user inputting a wallet nickname, then we
will have a cache of it's `WalletDetails` in LocalStorage. But those details may well be out of
date. This intermediate step makes sure we have the current details before proceeding.
This is also factored out into a separate handler so that it can be called directly when the user
selects a wallet nickname from the dropdown menu (as well as indirectly via the previous handler).
-}
handleAction (OpenUseWalletModalWithDetails walletDetails@{ companionAppId, walletNickname }) = do
  assign _remoteWalletDetails Loading
  ajaxWalletDetails <- lookupWalletDetails $ view _companionAppId walletDetails
  assign _remoteWalletDetails $ fromEither ajaxWalletDetails
  case ajaxWalletDetails of
    Left ajaxError -> openModal LocalWalletMissing
    Right _ -> openModal $ UseWallet walletNickname companionAppId

handleAction (WalletNicknameInputAction inputFieldAction) = toWalletNicknameInput $ InputField.handleAction inputFieldAction

{- [Workflow 2][2] Connect a wallet
This action is triggered by clicking the confirmation button on the UseWallet modal or
UseNewWallet modal. It saves the wallet nickname to LocalStorage, and then calls the
`MainFrame.EnterDashboardState` action.
-}
handleAction (ConnectWallet walletDetails@{ walletNickname }) = do
  assign _enteringDashboardState true
  modifying _walletLibrary (insert walletNickname walletDetails)
  insertIntoWalletLibrary walletDetails
  walletLibrary <- use _walletLibrary
  callMainFrameAction $ MainFrame.EnterDashboardState walletLibrary walletDetails

handleAction ClearLocalStorage = do
  clearAllLocalStorage
  liftEffect $ reload =<< location =<< window

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
toWalletNicknameInput =
  mapMaybeSubmodule
    (_modal <<< _Just <<< _1 <<< _UseNewWallet <<< _1)
    WalletNicknameInputAction
    InputField.dummyState
  where
  _UseNewWallet =
    prism' (uncurry UseNewWallet) case _ of
      UseNewWallet id nickname -> Just $ Tuple id nickname
      _ -> Nothing

------------------------------------------------------------
walletNicknameOrIdError :: WebData WalletDetails -> String -> Maybe WalletNicknameOrIdError
walletNicknameOrIdError remoteWalletDetails _ = case remoteWalletDetails of
  Loading -> Just UnconfirmedWalletNicknameOrId
  Failure _ -> Just NonexistentWalletNicknameOrId
  _ -> Nothing

------------------------------------------------------------
initialNicknameInputState :: WalletLibrary -> InputField.State WalletNicknameError
initialNicknameInputState walletLibrary =
  let
    state = InputField.dummyState :: InputField.State WalletNicknameError
  in
    state { validator = walletNicknameError walletLibrary }

openModal ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  MainFrameLoop m =>
  ManageMarlowe m =>
  ManageMarloweStorage m =>
  Toast m =>
  MonadClipboard m =>
  Modal ->
  HalogenM State Action ChildSlots Msg m Unit
openModal = handleAction <<< OpenModal
