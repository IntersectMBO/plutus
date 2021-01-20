module MainFrame.View where

import Prelude hiding (div)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.HTML (button, div, text)
import Halogen.HTML.Events (onClick)
import MainFrame.Types (Action(..), ChildSlots, State)

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div []
    [ button [ onClick $ const $ Just ClickedButton ] [ text "Click Me" ]
    ]
