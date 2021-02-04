module Welcome.View
  ( renderHome
  , renderContracts
  ) where

import Prelude hiding (div)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML, ClassName(ClassName))
import Halogen.HTML (HTML, button, div, span, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (classes)
import MainFrame.Types (Action(..), Card(..), ChildSlots, State)
import Material.Icons as Icon

renderHome :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
renderHome state =
  div
    [ classes $ ClassName <$> [ "p-1" ] ]
    [ div
        [ classes $ ClassName <$> [ "flex", "justify-between" ] ]
        [ span
            []
            [ text $ "State: " <> if state.on then "Why would you do that?!" else "Everything is OK" ]
        , button
            [ classes $ ClassName <$> [ "btn", "bg-blue", "text-white" ]
            , onClick $ const $ Just ClickedButton
            ]
            [ text "Click Me" ]
        ]
    , helpButton
    , addContractButton
    ]

renderContracts :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
renderContracts state =
  div
    [ classes $ ClassName <$> [ "p-1" ] ]
    [ text "Contracts"
    , helpButton
    , addContractButton
    ]

helpButton :: forall p. HTML p Action
helpButton =
  button
    [ classes $ ClassName <$> [ "btn", "absolute", "bottom-1", "left-1", "bg-blue", "text-white" ] ]
    [ Icon.help ]

addContractButton :: forall p. HTML p Action
addContractButton =
  button
    [ classes $ ClassName <$> [ "btn", "absolute", "bottom-1", "right-1", "bg-green", "text-white" ]
    , onClick $ const $ Just $ ToggleCard TemplateLibrary
    ]
    [ Icon.libraryAdd ]
