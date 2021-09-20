module MainFrame.View where

import Prelude hiding (div)
import Css (classNames)
import Halogen (ComponentHTML)
import Halogen.HTML (div, h1, text)
import MainFrame.Types (Action, ChildSlots, State)

render :: forall m. State -> ComponentHTML Action ChildSlots m
render state =
  div
    [ classNames [ "flex", "justify-center", "items-center", "h-screen" ]
    ]
    [ h1 [ classNames [ "text-xl", "font-bold" ] ] [ text "Empty shell for the marketplace" ] ]
