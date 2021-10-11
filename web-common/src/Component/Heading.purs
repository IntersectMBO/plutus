module Component.Heading (Preset(..), heading) where

import Prologue
import Component.Layout (Layout, layout)
import Halogen.HTML as HH

data Preset
  = H1
  | H2
  | H3
  | H4

heading :: Preset -> Layout
heading H1 = layout (commonStyles <> [ "text-xl" ]) HH.h1

heading H2 = layout (commonStyles <> [ "text-lg" ]) HH.h2

heading H3 = layout (commonStyles <> [ "text-base" ]) HH.h3

heading H4 = layout (commonStyles <> [ "text-sm" ]) HH.h4

commonStyles :: Array String
commonStyles = [ "font-semibold" ]
