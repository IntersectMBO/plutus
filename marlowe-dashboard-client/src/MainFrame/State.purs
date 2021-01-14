module MainFrame.State (mkMainFrame) where

import Prelude
import Data.Lens (modifying, use)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (Component, HalogenM, raise)
import Halogen as H
import Halogen.HTML (HTML)
import MainFrame.Types (Action(..), Msg(..), Query(..), State, ChildSlots, _on)
import MainFrame.View (render)
import WebSocket (StreamToServer(..))

initialState :: State
initialState = { on: true }

------------------------------------------------------------
mkMainFrame ::
  forall m.
  MonadAff m =>
  Component HTML Query Action Msg m
mkMainFrame =
  H.mkComponent
    { initialState: const initialState
    , render: render
    , eval:
        H.mkEval
          { handleQuery
          , handleAction
          , receive: const Nothing
          , initialize: Just Init
          , finalize: Nothing
          }
    }

handleQuery ::
  forall a m.
  Query a ->
  HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  current <- use _on
  modifying _on not
  pure $ Just next

handleAction ::
  forall m.
  MonadAff m =>
  Action ->
  HalogenM State Action ChildSlots Msg m Unit
handleAction Init = pure unit

handleAction ClickedButton = do
  current <- use _on
  raise (SendWebSocketMessage (ServerMsg current))
