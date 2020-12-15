module Modal.ViewHelpers
  ( modalHeaderTitle
  , modalHeaderWithClose
  ) where

import Prelude hiding (div)
import Data.Maybe (Maybe(..))
import Halogen (ComponentHTML)
import Halogen.Classes (closeModal)
import Halogen.HTML (ClassName(ClassName), HTML, div, h2, img, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, src)

modalHeaderTitle :: forall w i. String -> HTML w i
modalHeaderTitle title =
  div [ classes [ ClassName "modal-header" ] ]
    [ h2 [ classes [ ClassName "title" ] ] [ text title ]
    ]

modalHeaderWithClose ::
  forall m action slots.
  String ->
  action ->
  ComponentHTML action slots m
modalHeaderWithClose title closeAction =
  div [ classes [ ClassName "modal-header" ] ]
    [ h2 [ classes [ ClassName "title" ] ] [ text title ]
    , div [ class_ (ClassName "modal-close"), onClick $ const $ Just closeAction ]
        [ img [ src closeModal ] ]
    ]
