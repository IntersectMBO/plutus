module Hint.View (render) where

import Prelude hiding (div)
import Data.Maybe (Maybe(..))
import Halogen.Css (classNames, hideWhen)
import Halogen.HTML (HTML, div, fromPlainHTML)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (ref)
import Halogen.HTML.Properties.ARIA (role)
import Hint.Types (Action(..), State, arrowRef, hintRef, popoutRef)
import Material.Icons as Icon

render :: forall p. State -> HTML p Action
render state =
  div [ classNames $ [ "inline" ] <> state.hintElementClasses ]
    [ div
        [ classNames
            [ "cursor-pointer"
            , "inline"
            ]
        , onClick $ const $ Just Toggle
        , ref hintRef
        ]
        [ Icon.icon Icon.HelpOutline [ "text-purple", "text-xs" ] ]
    , div
        [ ref popoutRef
        , role "tooltip"
        , classNames
            ( [ "bg-white"
              , "rounded-sm"
              , "shadow-flat"
              , "z-50"
              -- The poput dialog has a min width in pixels (min-w-hint) and
              -- a max width set to min-content (max-w-min). The first property
              -- is straight forward, it guarantees that the width of the dialog
              -- will be at least the defined size. The second property defines
              -- the "breaking point", and it's calculated from the state.content's
              -- width.
              -- If we didn't provide a max-width, the dialog would occupy as much
              -- as possible, so it would never break. By setting the max-width to
              -- min-content it's up to state.content to define which is the minimum
              -- unbreakable width. This can be defined using `min-w-max` or
              -- `flex-shrink-0`.
              , "min-w-hint"
              , "max-w-min"
              ]
                <> hideWhen (not state.active)
            )
        ]
        [ div
            [ ref arrowRef
            , classNames [ "popover-arrow" ]
            ]
            []
        , div
            [ classNames [ "flex", "justify-end", "pt-2", "pr-2" ]
            , onClick $ const $ Just Close
            ]
            [ Icon.icon Icon.Close [ "cursor-pointer" ] ]
        , div
            [ classNames [ "p-4", "pt-0" ] ]
            [ fromPlainHTML state.content ]
        ]
    ]
