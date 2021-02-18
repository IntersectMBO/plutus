module Welcome.View (renderHome) where

import Prelude hiding (div)
import Css (buttonClasses, classNames, h2Classes)
import Data.Maybe (Maybe(..))
import Halogen.HTML (HTML, button, div, h2, span_, text)
import Halogen.HTML.Events (onClick)
import MainFrame.Types (Action(..), State)

renderHome :: forall p. State -> HTML p Action
renderHome state =
  div
    [ classNames [ "p-1" ] ]
    [ h2
        [ classNames h2Classes ]
        [ text "Dashboard home" ]
    , div
        [ classNames [ "flex", "justify-between" ] ]
        [ span_
            [ text $ "State: " <> if state.on then "Why would you do that?!" else "Everything is OK" ]
        , button
            [ classNames $ buttonClasses <> [ "bg-blue", "text-white" ]
            , onClick $ const $ Just ClickedButton
            ]
            [ text "Click Me" ]
        ]
    ]
