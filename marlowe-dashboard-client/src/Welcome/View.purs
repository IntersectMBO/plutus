module Welcome.View
  ( renderHome
  , renderContracts
  ) where

import Prelude hiding (div)
import Css (classNames)
import Data.Maybe (Maybe(..))
import Halogen.HTML (HTML, button, div, span, text)
import Halogen.HTML.Events (onClick)
import MainFrame.Types (Action(..), Card(..), ContractInstance, ContractStatus, State)
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
            [ classNames [ "btn", "bg-blue", "text-white" ]
            , onClick $ const $ Just ClickedButton
            ]
            [ text "Click Me" ]
        ]
    , helpButton
    , addContractButton
    ]

renderContracts :: forall p. Array ContractInstance -> ContractStatus -> HTML p Action
renderContracts contracts contractStatus =
  div
    [ classNames [ "p-1" ] ]
    [ text "Contracts"
    , helpButton
    , addContractButton
    ]

helpButton :: forall p. HTML p Action
helpButton =
  button
    [ classNames [ "btn", "absolute", "bottom-1", "left-1", "bg-blue", "text-white" ] ]
    [ Icon.help ]

addContractButton :: forall p. HTML p Action
addContractButton =
  button
    [ classNames [ "btn", "absolute", "bottom-1", "right-1", "bg-green", "text-white" ]
    , onClick $ const $ Just $ ToggleCard TemplateLibrary
    ]
    [ Icon.libraryAdd ]
