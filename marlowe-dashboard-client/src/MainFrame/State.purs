module MainFrame.State (mkMainFrame) where

import Prelude
import Contact.Lenses (_contacts)
import Contact.State (handleAction, initialState) as Contact
import Contact.Types (Action(..)) as Contact
import Contract.State (handleAction, initialState) as Contract
import Contract.Types (Action(..)) as Contract
import Contract.Types (_executionState)
import Control.Monad.Except (runExcept)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, set, use)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Foreign.Generic (decode)
import Foreign.JSON (parseJSON)
import Halogen (Component, HalogenM, liftEffect, mkComponent, mkEval, modify_, raise)
import Halogen.Extra (mapSubmodule)
import Halogen.HTML (HTML)
import LocalStorage (getItem)
import MainFrame.Lenses (_card, _contactState, _contractState, _on, _overlay, _screen)
import MainFrame.Types (Action(..), Card(..), ChildSlots, Msg(..), Query(..), Screen(..), State)
import MainFrame.View (render)
import Marlowe.Execution (_contract)
import Marlowe.Semantics (Contract(..))
import StaticData (contactsLocalStorageKey)
import WebSocket (StreamToClient(..), StreamToServer(..))
import WebSocket.Support as WS

mkMainFrame :: forall m. MonadAff m => Component HTML Query Action Msg m
mkMainFrame =
  mkComponent
    { initialState: const initialState
    , render: render
    , eval:
        mkEval
          { handleQuery
          , handleAction
          , receive: const Nothing
          , initialize: Just Init
          , finalize: Nothing
          }
    }

initialState :: State
initialState =
  { overlay: Nothing
  , screen: Home
  , card: Nothing
  , contactState: Contact.initialState
  , contractState: Contract.initialState zero Close
  , notifications: []
  , templates: []
  , contracts: []
  , on: true
  }

handleQuery :: forall a m. Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  case msg of
    (WS.ReceiveMessage (Right (ClientMsg on))) -> assign _on on
    -- TODO: other matches such as update current slot or apply transaction
    _ -> pure unit
  pure $ Just next

handleAction :: forall m. MonadAff m => Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction Init = do
  mCachedContactsJson <- liftEffect $ getItem contactsLocalStorageKey
  for_ mCachedContactsJson
    $ \json -> do
        let
          contacts =
            runExcept
              $ do
                  foreignJson <- parseJSON json
                  decode foreignJson
        case contacts of
          Right cachedContacts -> assign (_contactState <<< _contacts) cachedContacts
          _ -> pure unit

handleAction (ToggleOverlay overlay) = do
  mCurrentOverlay <- use _overlay
  case mCurrentOverlay of
    Just currentOverlay
      | overlay == currentOverlay -> assign _overlay Nothing
    _ -> assign _overlay $ Just overlay

handleAction (SetScreen screen) =
  modify_
    ( set _overlay Nothing
        <<< set _card Nothing
        <<< set _screen screen
    )

handleAction (ToggleCard card) = do
  assign _overlay Nothing
  mCurrentCard <- use _card
  case mCurrentCard of
    Just currentCard
      | card == currentCard -> assign _card Nothing
    _ -> assign _card $ Just card

handleAction CloseCard = assign _card Nothing

handleAction (ContactAction contactAction) = do
  mapSubmodule _contactState ContactAction $ Contact.handleAction contactAction
  case contactAction of
    Contact.ToggleNewContactCard -> handleAction $ ToggleCard NewContact
    Contact.AddNewContact -> handleAction $ ToggleCard NewContact
    Contact.ToggleEditContactCard contactKey -> handleAction $ ToggleCard $ EditContact contactKey
    _ -> pure unit

handleAction (ContractAction contractAction) = do
  contractState <- use _contractState
  case contractAction of
    Contract.ClosePanel -> pure unit
    action -> mapSubmodule _contractState ContractAction $ Contract.handleAction action

handleAction ClickedButton = do
  current <- use _on
  raise (SendWebSocketMessage (ServerMsg current))

handleAction (StartContract contract) = do
  assign (_contractState <<< _executionState <<< _contract) contract
