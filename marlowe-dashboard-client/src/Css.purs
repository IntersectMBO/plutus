module Css
  ( classNames
  , applyWhen
  , hideWhen
  ) where

import Prelude
import Halogen (ClassName(ClassName))
import Halogen.HTML.Properties (IProp, classes)

classNames :: forall r i. Array String -> IProp ( class :: String | r ) i
classNames = classes <<< map ClassName

applyWhen :: Boolean -> String -> Array String
applyWhen condition className = if condition then [ className ] else []

hideWhen :: Boolean -> Array String
hideWhen condition = applyWhen condition "hidden"
