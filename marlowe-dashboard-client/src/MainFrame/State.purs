module MainFrame.State (mkMainFrame) where

import Prelude
import Contact.Lenses (_contacts)
import Contact.State (handleAction, initialState) as Contact
import Contact.Types (Action(..)) as Contact
import Control.Monad.Except (runExcept)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, modifying, set, use)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Foreign.Generic (decode)
import Foreign.JSON (parseJSON)
import Halogen (Component, HalogenM, liftEffect, mkComponent, mkEval, modify_, raise)
import Halogen.Extra (mapSubmodule)
import Halogen.HTML (HTML)
import LocalStorage (getItem)
import MainFrame.Lenses (_card, _contactState, _on, _overlay, _screen)
import MainFrame.Types (Action(..), Card(..), ChildSlots, Msg(..), Query(..), Screen(..), State)
import MainFrame.View (render)
import StaticData (contactsLocalStorageKey)
import WebSocket (StreamToServer(..))

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
  , notifications: []
  , templates: []
  , contracts: []
  , on: true
  }

handleQuery :: forall a m. Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  current <- use _on
  modifying _on not
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

handleAction ClickedButton = do
  current <- use _on
  raise (SendWebSocketMessage (ServerMsg current))
