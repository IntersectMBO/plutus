module Notifications.View (renderNotifications) where

import Prelude hiding (div)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML, ClassName(ClassName))
import Halogen.HTML (button, div, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (classes)
import MainFrame.Types (Action(..), ChildSlots, Notification, Overlay(..))
import Material.Icons as Icon

renderNotifications :: forall m. MonadAff m => Maybe Overlay -> Array Notification -> ComponentHTML Action ChildSlots m
renderNotifications overlay notifications =
  div
    [ classes $ ClassName <$> [ "notifications" ] <> if overlay == Just Notifications then [] else [ "hidden" ] ]
    [ button
        [ classes $ ClassName <$> [ "btn", "text-green", "float-right" ]
        , onClick $ const $ Just $ ToggleOverlay Notifications
        ]
        [ Icon.close ]
    , text "Notifications"
    ]
