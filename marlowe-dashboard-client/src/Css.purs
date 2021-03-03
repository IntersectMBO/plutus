module Css
  ( classNames
  , toggleWhen
  , applyWhen
  , hideWhen
  , button
  , primaryButton
  , secondaryButton
  , fixedPrimaryButton
  , input
  , inputError
  , hasNestedLabel
  , nestedLabel
  , cardWrapper
  , card
  , largeCard
  ) where

import Prelude
import Halogen (ClassName(ClassName))
import Halogen.HTML.Properties (IProp, classes)

classNames :: forall r i. Array String -> IProp ( class :: String | r ) i
classNames = classes <<< map ClassName

toggleWhen :: Boolean -> Array String -> Array String -> Array String
toggleWhen condition classes1 classes2 = if condition then classes1 else classes2

applyWhen :: Boolean -> Array String -> Array String
applyWhen condition classes = if condition then classes else []

hideWhen :: Boolean -> Array String
hideWhen condition = applyWhen condition [ "hidden" ]

------------------------------------------------------------
button :: Array String
button = [ "flex", "items-center", "justify-center", "px-1", "py-0.75", "leading-none", "disabled:opacity-50", "disabled:cursor-not-allowed", "rounded-3xl" ]

primaryButton :: Array String
primaryButton = button <> [ "bg-gradient-to-r", "from-blue", "to-lightblue", "text-white", "shadow-lg" ]

secondaryButton :: Array String
secondaryButton = button <> [ "bg-gray", "text-black" ]

fixedPrimaryButton :: Array String
fixedPrimaryButton = primaryButton <> [ "absolute", "bottom-1", "right-1" ]

input :: Boolean -> Array String
input invalid = [ "block", "w-full", "border", "border-darkgray", "py-0.5", "px-0.75", "rounded-lg" ] <> applyWhen invalid [ "border-red" ]

inputError :: Array String
inputError = [ "text-red", "text-sm" ]

hasNestedLabel :: Array String
hasNestedLabel = [ "-mt-1.5" ]

nestedLabel :: Array String
nestedLabel = [ "relative", "left-0.5", "top-0.75", "px-0.25", "bg-white", "text-sm" ]

cardWrapper :: Boolean -> Array String
cardWrapper invisible = [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "z-10", "flex", "flex-col", "justify-end", "md:justify-center", "bg-transgray" ] <> hideWhen invisible

card :: Array String
card = [ "shadow-lg", "bg-white", "mx-1", "rounded-t-lg", "md:mx-auto", "md:w-22", "md:rounded-b-lg" ]

largeCard :: Array String
largeCard = [ "shadow-lg", "max-h-full", "overflow-auto", "bg-gray", "mt-3", "mx-1", "rounded-t-lg", "md:rounded-b-lg", "md:mb-3", "lg:mx-3" ]
