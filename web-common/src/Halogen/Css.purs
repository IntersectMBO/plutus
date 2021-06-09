module Halogen.Css
  ( classNames
  , applyWhen
  , hideWhen
  ) where

import Prelude
import Halogen (ClassName(ClassName))
import Halogen.HTML.Properties (IProp, classes)

classNames :: forall r i. Array String -> IProp ( class :: String | r ) i
classNames = classes <<< map ClassName

--- utilities
applyWhen :: Boolean -> Array String -> Array String
applyWhen true classes = classes

applyWhen false _ = []

hideWhen :: Boolean -> Array String
hideWhen = flip applyWhen [ "hidden" ]
