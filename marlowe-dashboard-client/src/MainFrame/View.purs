module MainFrame.View where

import Prelude hiding (div)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.HTML (div)
import MainFrame.Types (Action, ChildSlots, State)

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state = div [] []
