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
  , inputDark
  , inputError
  , hasNestedLabel
  , nestedLabel
  , cardWrapper
  , card
  , largeCard
  , iconCircle
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
button = [ "flex", "items-center", "justify-center", "px-4", "py-3", "leading-none", "font-bold", "disabled:opacity-50", "disabled:cursor-not-allowed", "rounded-3xl" ]

primaryButton :: Array String
primaryButton = button <> [ "bg-gradient-to-r", "from-blue", "to-lightblue", "text-white", "shadow" ]

secondaryButton :: Array String
secondaryButton = button <> [ "bg-gray", "text-black" ]

fixedPrimaryButton :: Array String
fixedPrimaryButton = primaryButton <> [ "absolute", "bottom-4", "right-4" ]

inputBase :: Array String
inputBase = [ "block", "w-full", "border", "px-4", "py-3", "rounded-lg" ]

input :: Boolean -> Array String
input invalid = inputBase <> toggleWhen invalid [ "border-red" ] [ "border-darkgray" ]

inputDark :: Boolean -> Array String
inputDark invalid = inputBase <> toggleWhen invalid [ "border-red" ] [ "border-black" ]

inputError :: Array String
inputError = [ "text-red", "text-sm" ]

hasNestedLabel :: Array String
hasNestedLabel = [ "-mt-6" ]

nestedLabel :: Array String
nestedLabel = [ "relative", "left-2", "top-2.5", "px-1", "bg-white", "text-xs" ]

cardWrapper :: Boolean -> Array String
cardWrapper invisible = [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "z-20", "flex", "flex-col", "justify-end", "md:justify-center", "bg-transgray" ] <> hideWhen invisible

card :: Array String
card = [ "shadow", "bg-white", "mx-4", "rounded-t-lg", "md:mx-auto", "md:w-96", "md:rounded-b-lg" ]

largeCard :: String -> Array String
largeCard bgColor = [ "shadow", "max-h-full", "overflow-auto", "mt-12", "mx-4", "rounded-t-lg", "md:rounded-b-lg", "md:mb-12", "lg:mx-12", bgColor ]

iconCircle :: Boolean -> Array String
iconCircle enabled = [ "inline-flex", "items-center", "justify-center", "w-10", "h-10", "rounded-full" ] <> toggleWhen enabled [ "bg-gradient-to-r", "from-blue", "to-lightblue", "text-white" ] [ "bg-gray", "text-darkgray" ]
