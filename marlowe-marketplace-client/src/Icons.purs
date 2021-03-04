module Material.Icons
  ( help
  ) where

import Prelude
import Halogen.HTML (ClassName(ClassName), HTML, span, text)
import Halogen.HTML.Properties (class_)

icon :: forall p i. String -> HTML p i
icon str = span [ class_ $ ClassName "material-icons" ] [ text str ]

-----
help :: forall p i. HTML p i
help = icon "help"
