module LoadingSubmitButton.View (render) where

import Prelude hiding (div)
import Css as Css
import Data.Maybe (Maybe(..))
import Halogen.Css (classNames)
import Halogen.HTML (HTML, div, text, button)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (disabled, ref)
import LoadingSubmitButton.Types (Action(..), State, buttonRef)
import Material.Icons as Icon
import Network.RemoteData (RemoteData(..))

render :: forall p. State -> HTML p Action
render { caption, styles, status, enabled } =
  let
    withWidthAnimation = [ "transition-width", "duration-200" ]

    resultClasses = Css.button <> withWidthAnimation <> [ "w-full", "border-2", "flex", "items-center", "justify-center", "cursor-default" ]

    classes = case status of
      NotAsked -> Css.button <> Css.bgBlueGradient <> Css.withShadow <> withWidthAnimation <> [ "w-full" ]
      Loading ->
        [ "border-4"
        , "border-gray"
        , "border-left-green"
        , "rounded-full"
        , "cursor-default"
        , "outline-none"
        , "focus:outline-none"
        ]
          <> withWidthAnimation
      Success msg -> resultClasses <> [ "border-green", "text-green" ]
      Failure msg -> resultClasses <> [ "border-red", "text-red" ]

    content = case status of
      NotAsked -> [ text caption ]
      Loading -> []
      Success msg -> [ Icon.icon Icon.TaskAlt [ "font-normal", "mr-2" ], text msg ]
      Failure msg -> [ text msg ]
  in
    div
      [ classNames $ styles <> [ "flex", "justify-center" ] ]
      [ button
          [ classNames classes
          , ref buttonRef
          , disabled $ not enabled
          , onClick \_ -> case status of
              NotAsked -> Just Submit
              _ -> Nothing
          ]
          content
      ]
