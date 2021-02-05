module Notifications.View (renderNotifications) where

import Prelude hiding (div)
import Css (classNames, hideWhen)
import Data.Maybe (Maybe(..))
import Halogen.HTML (HTML, button, div, text)
import Halogen.HTML.Events (onClick)
import MainFrame.Types (Action(..), Notification, Overlay(..))
import Material.Icons as Icon

renderNotifications :: forall p. Maybe Overlay -> Array Notification -> HTML p Action
renderNotifications overlay notifications =
  div
    [ classNames $ [ "notifications" ] <> hideWhen (overlay /= Just Notifications) ]
    [ button
        [ classNames [ "btn", "text-green", "float-right" ]
        , onClick $ const $ Just $ ToggleOverlay Notifications
        ]
        [ Icon.close ]
    , text "Notifications"
    ]
