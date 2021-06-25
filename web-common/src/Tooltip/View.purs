module Tooltip.View (render) where

import Prelude hiding (div)
import Halogen.Css (classNames, hideWhen)
import Halogen.HTML (HTML, div, text)
import Halogen.HTML.Properties (ref)
import Halogen.HTML.Properties.ARIA (role)
import Tooltip.Types (State, tooltipRef, arrowRef)

render :: forall p action. State -> HTML p action
render state =
  div
    [ ref tooltipRef
    , role "tooltip"
    , classNames
        ( [ "tooltip", "bg-black", "p-2", "rounded-sm", "text-white", "text-sm", "z-50" ]
            <> hideWhen (not state.active)
        )
    ]
    [ div
        [ ref arrowRef
        , classNames [ "tooltip-arrow" ]
        ]
        []
    , text
        $ state.message
    ]
