module MainFrame.State (mkMainFrame) where

import Prelude
import Control.Monad.Reader (class MonadAsk)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (Component, HalogenM, defaultEval, mkComponent, mkEval)
import Halogen.HTML (HTML)
import MainFrame.Types (Action(..), ChildSlots, State)
import MainFrame.View (render)

mkMainFrame ::
  forall m query msg.
  MonadAff m =>
  MonadAsk Env m =>
  Component HTML query Action msg m
mkMainFrame =
  mkComponent
    { initialState: const initialState
    , render: render
    , eval:
        mkEval
          $ defaultEval
              { handleAction = handleAction
              , initialize = Just Init
              }
    }

initialState :: State
initialState =
  { placeholder: "some value"
  }

handleAction ::
  forall m msg.
  MonadAff m =>
  MonadAsk Env m =>
  Action -> HalogenM State Action ChildSlots msg m Unit
handleAction Init = pure unit
