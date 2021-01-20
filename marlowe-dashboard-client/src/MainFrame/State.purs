module MainFrame.State (mkMainFrame) where

import Prelude
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (Component, HalogenM)
import Halogen as H
import Halogen.HTML (HTML)
import MainFrame.Types (Action(..), State, ChildSlots, Query)
import MainFrame.View (render)

initialState :: State
initialState = {}

------------------------------------------------------------
mkMainFrame ::
  forall m.
  MonadAff m =>
  Component HTML Query Unit Void m
mkMainFrame =
  H.mkComponent
    { initialState: const initialState
    , render: render
    , eval:
        H.mkEval
          { handleQuery: const $ pure Nothing
          , handleAction
          , receive: const Nothing
          , initialize: Just Init
          , finalize: Nothing
          }
    }

handleAction ::
  forall m.
  MonadAff m =>
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction Init = pure unit
