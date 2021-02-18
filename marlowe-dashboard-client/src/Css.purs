module Css
  ( classNames
  , toggleWhen
  , applyWhen
  , hideWhen
  , h2Classes
  , buttonClasses
  , textInputClasses
  ) where

import Prelude
import Halogen (ClassName(ClassName))
import Halogen.HTML.Properties (IProp, classes)

classNames :: forall r i. Array String -> IProp ( class :: String | r ) i
classNames = classes <<< map ClassName

toggleWhen :: Boolean -> String -> String -> Array String
toggleWhen condition className1 className2 = if condition then [ className1 ] else [ className2 ]

applyWhen :: Boolean -> String -> Array String
applyWhen condition className = if condition then [ className ] else []

hideWhen :: Boolean -> Array String
hideWhen condition = applyWhen condition "hidden"

h2Classes :: Array String
h2Classes =
  [ "font-bold"
  , "text-lg"
  , "mb-1"
  ]

buttonClasses :: Array String
buttonClasses =
  [ "p-0.5"
  , "leading-none"
  , "focus:outline-none"
  , "disabled:opacity-50"
  , "disabled:cursor-not-allowed"
  ]

textInputClasses :: Array String
textInputClasses =
  [ "border"
  , "p-0.5"
  ]
