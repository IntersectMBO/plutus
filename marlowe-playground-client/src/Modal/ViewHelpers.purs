module Modal.ViewHelpers
  ( modalHeaderTitle
  ) where

import Halogen.HTML (ClassName(ClassName), HTML, div, h2, text)
import Halogen.HTML.Properties (classes)

modalHeaderTitle :: forall w i. String -> HTML w i
modalHeaderTitle title =
  div [ classes [ ClassName "modal-header" ] ]
    [ h2 [ classes [ ClassName "title" ] ] [ text title ]
    ]
