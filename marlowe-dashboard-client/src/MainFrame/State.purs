module MainFrame.State (mkMainFrame) where

import Prelude
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (Component, HalogenM, raise)
import Halogen as H
import Halogen.HTML (HTML)
import MainFrame.Types (Action(..), ChildSlots, Msg(..), Query(..), State)
import MainFrame.View (render)
import WebSocket (StreamToServer(..))

initialState :: State
initialState = {}

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
  Monad m =>
  Query a -> m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = pure $ Just next

handleAction ::
  forall m.
  MonadAff m =>
  Action ->
  HalogenM State Action ChildSlots Msg m Unit
handleAction Init = pure unit

handleAction ClickedButton = raise (SendWebSocketMessage ServerMsg)
