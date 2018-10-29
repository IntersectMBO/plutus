module Bootstrap where

import Data.Monoid ((<>))
import Halogen.HTML (ClassName(..), HTML, div)
import Halogen.HTML.Properties (classes)

container :: forall p i. Array (HTML p i) -> HTML p i
container =
  div
    [ classes [ ClassName "container" ] ]

btn :: ClassName
btn = ClassName "btn "

btnPrimary :: ClassName
btnPrimary = btn <> ClassName "btn-primary "

btnSecondary :: ClassName
btnSecondary = btn <> ClassName "btn-secondary "
