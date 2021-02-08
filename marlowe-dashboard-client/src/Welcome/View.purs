module Welcome.View (renderHome) where

import Prelude hiding (div)
import Css (buttonClasses, classNames)
import Data.Maybe (Maybe(..))
import Halogen.HTML (HTML, button, div, span, text)
import Halogen.HTML.Events (onClick)
import MainFrame.Types (Action(..), Card(..), State)
import Material.Icons as Icon

renderHome :: forall p. State -> HTML p Action
renderHome state =
  div
    [ classNames [ "p-1" ] ]
    [ div
        [ classNames [ "flex", "justify-between" ] ]
        [ span
            []
            [ text $ "State: " <> if state.on then "Why would you do that?!" else "Everything is OK" ]
        , button
            [ classNames $ buttonClasses <> [ "bg-blue", "text-white" ]
            , onClick $ const $ Just ClickedButton
            ]
            [ text "Click Me" ]
        ]
    , button
        [ classNames $ bottomButtonClasses <> [ "left-1" ] ]
        [ Icon.help ]
    , button
        [ classNames $ bottomButtonClasses <> [ "right-1" ]
        , onClick $ const $ Just $ ToggleCard TemplateLibrary
        ]
        [ Icon.libraryAdd ]
    ]
  where
  bottomButtonClasses = buttonClasses <> [ "absolute", "bottom-1", "bg-green", "text-white" ]
