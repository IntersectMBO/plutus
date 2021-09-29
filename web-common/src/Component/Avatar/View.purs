module Component.Avatar.View
  ( avatar
  , avatarWithChildren
  ) where

import Prologue hiding (div)
import Component.Avatar.Types (Input, Size(..))
import Data.String (take)
import Halogen.Css (classNames)
import Halogen.HTML (HTML, div, span, text)

avatar :: forall w action. Input -> HTML w action
avatar input = avatarWithChildren input pure

avatarWithChildren ::
  forall w action.
  Input ->
  (HTML w action -> Array (HTML w action)) ->
  HTML w action
avatarWithChildren { background, nickname, size } avatarChildren =
  div
    [ classNames
        $ [ "flex"
          , "items-center"
          , "justify-center"
          , "rounded-full"
          ]
        <> background
        <> case size of
            Small ->
              [ "h-5"
              , "w-5"
              ]
            Medium ->
              [ "h-10"
              , "w-10"
              ]
            Large ->
              [ "h-25"
              , "w-25"
              ]
    ]
    $ avatarChildren
    $ span [ classNames [ "text-sm", "uppercase", "font-semibold", "text-white" ] ]
        [ text $ take 1 nickname ]
