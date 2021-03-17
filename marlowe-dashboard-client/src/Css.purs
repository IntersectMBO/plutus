module Css
  ( classNames
  , toggleWhen
  , applyWhen
  , hideWhen
  , bgBlueGradiant
  , button
  , withIcon
  , withShadow
  , primaryButton
  , secondaryButton
  , whiteButton
  , input
  , inputCard
  , inputError
  , hasNestedLabel
  , nestedLabel
  , overlay
  , cardWrapper
  , card
  , largeCardWrapper
  , largeCard
  , iconCircle
  , fixedBottomRight
  ) where

import Prelude
import Halogen (ClassName(ClassName))
import Halogen.HTML.Properties (IProp, classes)
import Material.Icons (Icon, iconClass)

classNames :: forall r i. Array String -> IProp ( class :: String | r ) i
classNames = classes <<< map ClassName

--- utilities
toggleWhen :: Boolean -> Array String -> Array String -> Array String
toggleWhen condition classes1 classes2 = if condition then classes1 else classes2

applyWhen :: Boolean -> Array String -> Array String
applyWhen condition classes = if condition then classes else []

hideWhen :: Boolean -> Array String
hideWhen condition = applyWhen condition [ "hidden" ]

--- color gradiant
bgBlueGradiant :: Array String
bgBlueGradiant = [ "bg-gradient-to-r", "from-blue", "to-lightblue", "text-white" ]

-- buttons
button :: Array String
button = [ "leading-none", "whitespace-nowrap", "px-4", "py-3", "font-black", "rounded-lg", "transition-all", "duration-200", "hover:shadow", "outline-none", "focus:outline-none", "disabled:bg-none", "disabled:bg-lightgray", "disabled:text-darkgray", "disabled:shadow-none" ]

withShadow :: Array String
withShadow = [ "shadow", "hover:shadow-lg" ]

primaryButton :: Array String
primaryButton = button <> bgBlueGradiant <> withShadow

secondaryButton :: Array String
secondaryButton = button <> [ "bg-lightgray", "text-black" ]

whiteButton :: Array String
whiteButton = button <> withShadow <> [ "bg-white" ]

withIcon :: Icon -> Array String
withIcon icon = [ "with-icon", "with-icon-" <> iconClass icon ]

--- inputs
inputBase :: Array String
inputBase = [ "block", "w-full", "border", "p-3", "rounded", "transition-all", "duration-200", "outline-none", "focus:outline-none" ]

input :: Boolean -> Array String
input invalid = inputBase <> [ "hover:shadow", "focus:shadow" ] <> toggleWhen invalid [ "border-red" ] [ "border-gray", "hover:border-black", "focus:border-black" ]

inputCard :: Boolean -> Array String
inputCard invalid = inputBase <> [ "shadow-sm", "hover:shadow", "focus:shadow" ] <> toggleWhen invalid [ "border-red" ] [ "border-transparent" ]

inputError :: Array String
inputError = [ "text-red", "text-sm" ]

hasNestedLabel :: Array String
hasNestedLabel = [ "-mt-3" ]

nestedLabel :: Array String
nestedLabel = [ "relative", "left-2", "top-2", "px-1", "bg-white", "text-xs" ]

--- cards
overlay :: Boolean -> Array String
overlay invisible = [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "z-20", "flex", "flex-col", "justify-end", "md:justify-center", "bg-overlay", "transition-opacity", "duration-400" ] <> toggleWhen invisible [ "opacity-0", "pointer-events-none" ] [ "opacity-1" ]

cardWrapper :: Array String
cardWrapper = [ "w-sm", "mx-auto", "px-3" ]

card :: Boolean -> Array String
card invisible = [ "w-full", "shadow", "bg-white", "p-4", "pb-6", "rounded-t", "md:p-6", "md:pb-10", "md:rounded-b", "transform", "transition-transform", "duration-400" ] <> applyWhen invisible [ "translate-y-10" ]

largeCardWrapper :: Array String
largeCardWrapper = [ "max-h-full", "pt-3", "px-3", "md:py-3", "md:px-5pc" ]

largeCard :: Boolean -> String -> Array String
largeCard invisible bgColor = [ "shadow", "max-h-full", "w-full", "overflow-auto", "p-4", "rounded-t", "md:rounded-b", "md:mb-6", "lg:mx-6", "transform", "transition-transform", "duration-400", bgColor ] <> applyWhen invisible [ "translate-y-10" ]

--largeCard :: Array String
--largeCard = [ "shadow", "h-full", "overflow-auto", "mt-2", "md:mb-2", "mx-2", "rounded-t-lg", "md:rounded-b-lg", "lg:mx-12", "bg-grayblue" ]
--- miscellaneous
iconCircle :: Boolean -> Array String
iconCircle enabled = [ "inline-flex", "items-center", "justify-center", "w-6", "h-6", "rounded-full" ] <> toggleWhen enabled bgBlueGradiant [ "bg-lightgray", "text-darkgray" ]

fixedBottomRight :: Array String
fixedBottomRight = [ "absolute", "bottom-3", "right-3", "md:right-5pc" ]
