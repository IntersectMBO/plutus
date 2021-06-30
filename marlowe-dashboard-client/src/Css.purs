module Css
  ( bgBlueGradient
  , button
  , withIcon
  , withShadow
  , primaryButton
  , secondaryButton
  , whiteButton
  , input
  , inputNoFocus
  , inputCard
  , inputCardNoFocus
  , inputError
  , hasNestedLabel
  , nestedLabel
  , withNestedLabel
  , overlay
  , card
  , largeCard
  , videoCard
  , embeddedVideoContainer
  , embeddedVideo
  , iconCircle
  , fixedBottomRight
  , funds
  ) where

import Prelude
import Halogen.Css (applyWhen)
import Material.Icons (Icon, iconClass)

--- color gradients
bgBlueGradient :: Array String
bgBlueGradient = [ "bg-gradient-to-r", "from-purple", "to-lightpurple", "text-white" ]

-- buttons
button :: Array String
button =
  [ "px-6"
  , "py-4"
  , "rounded-full"
  , "font-bold"
  , "leading-none"
  , "whitespace-nowrap"
  , "transition-all"
  , "duration-200"
  , "outline-none"
  , "focus:outline-none"
  , "disabled:bg-none"
  , "disabled:bg-lightgray"
  , "disabled:text-darkgray"
  , "disabled:shadow-none"
  ]

withShadow :: Array String
withShadow = [ "shadow", "hover:shadow-lg" ]

primaryButton :: Array String
primaryButton = button <> bgBlueGradient <> withShadow

secondaryButton :: Array String
secondaryButton = button <> [ "bg-lightgray", "text-black", "hover:shadow" ]

whiteButton :: Array String
whiteButton = button <> withShadow <> [ "bg-white" ]

withIcon :: Icon -> Array String
withIcon icon = [ "with-icon", "with-icon-" <> iconClass icon ]

--- inputs
inputBase :: Array String
inputBase =
  [ "block"
  , "w-full"
  , "p-4"
  , "rounded"
  , "transition-all"
  , "duration-200"
  , "outline-none"
  , "focus:outline-none"
  , "text-black"
  , "border-transparent"
  , "focus:border-transparent"
  , "shadow-sm"
  , "focus:shadow"
  , "hover:shadow"
  ]

inputBaseFocus :: Array String
inputBaseFocus = inputBase <> [ "focus:ring-1" ]

inputBaseNoFocus :: Array String
inputBaseNoFocus = inputBase <> [ "focus:ring-0" ]

input :: Boolean -> Array String
input valid = inputBaseFocus <> [ "border", "bg-transparent" ] <> if valid then [ "border-black", "focus:border-black" ] else [ "border-red" ]

inputNoFocus :: Boolean -> Array String
inputNoFocus valid = inputBaseNoFocus <> if valid then [ "border-transparent" ] else [ "border-red" ]

withNestedLabel :: Array String
withNestedLabel = [ "border", "border-gray", "focus:border-gray" ]

inputCard :: Boolean -> Array String
inputCard valid = inputBaseFocus <> if valid then [ "border-transparent" ] else [ "border-red" ]

inputCardNoFocus :: Boolean -> Array String
inputCardNoFocus valid = inputBaseNoFocus <> if valid then [ "border-transparent" ] else [ "border-red" ]

inputError :: Array String
inputError = [ "px-3", "mt-1", "text-red", "text-sm" ]

hasNestedLabel :: Array String
hasNestedLabel = [ "-mt-4" ]

nestedLabel :: Array String
nestedLabel = [ "relative", "z-10", "left-2", "top-2.5", "px-1", "bg-white", "text-xs", "font-semibold" ]

--- cards
overlay :: Boolean -> Array String
overlay visible = [ "overflow-hidden", "absolute", "inset-0", "z-20", "flex", "justify-center", "content-end", "md:content-center", "last:bg-overlay", "transition-opacity", "duration-400" ] <> if visible then [ "opacity-1" ] else [ "opacity-0", "pointer-events-none" ]

card :: Boolean -> Array String
card visible = [ "overflow-hidden", "bg-white", "flex-grow", "max-w-sm", "mx-2", "shadow", "rounded-t", "md:rounded-b", "transform", "transition-transform", "duration-400", "self-end", "md:self-center" ] <> applyWhen (not visible) [ "translate-y-20" ]

largeCard :: Boolean -> Array String
largeCard visible = [ "bg-grayblue", "shadow", "overflow-auto", "flex-grow", "mt-2", "md:mb-2", "mx-2", "lg:my-4", "md:mx-5pc", "rounded-t", "md:rounded-b", "transform", "transition-transform", "duration-400" ] <> applyWhen (not visible) [ "translate-y-20" ]

videoCard :: Boolean -> Array String
videoCard visible = [ "relative", "bg-white", "flex-grow", "max-w-sm", "lg:max-w-md", "mx-2", "shadow", "rounded", "transform", "transition-transform", "duration-400", "self-center" ] <> applyWhen (not visible) [ "translate-y-20" ]

-- embedded videos
embeddedVideoContainer :: Array String
embeddedVideoContainer = [ "relative", "pb-16:9" ]

embeddedVideo :: Array String
embeddedVideo = [ "absolute", "top-0", "left-0", "w-full", "h-full" ]

--- miscellaneous
iconCircle :: Boolean -> Array String
iconCircle enabled = [ "inline-flex", "items-center", "justify-center", "w-8", "h-8", "rounded-full" ] <> if enabled then bgBlueGradient else [ "bg-lightgray", "text-darkgray" ]

fixedBottomRight :: Array String
fixedBottomRight = [ "absolute", "bottom-4", "right-4", "md:right-5pc" ]

funds :: Array String
funds = [ "text-2xl", "text-purple", "font-semibold" ]
