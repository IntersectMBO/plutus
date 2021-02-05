module MainFrame.State (mkMainFrame) where

import Prelude
import Data.Lens (assign, modifying, set, use)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (Component, HalogenM, mkComponent, mkEval, modify_, raise)
import Halogen.HTML (HTML)
import MainFrame.Lenses (_card, _on, _overlay, _screen)
import MainFrame.Types (Action(..), ChildSlots, Msg(..), Query(..), Screen(..), State)
import MainFrame.View (render)
import WebSocket (StreamToServer(..))

initialState :: State
initialState =
  { overlay: Nothing
  , screen: Home
  , card: Nothing
  , notifications: []
  , templates: []
  , contracts: []
  , on: true
  }

------------------------------------------------------------
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

handleQuery :: forall a m. Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  current <- use _on
  modifying _on not
  pure $ Just next

handleAction :: forall m. MonadAff m => Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction Init = pure unit

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

handleAction ClickedButton = do
  current <- use _on
  raise (SendWebSocketMessage (ServerMsg current))
