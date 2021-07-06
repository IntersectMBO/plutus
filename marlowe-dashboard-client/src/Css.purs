module Css
  ( container
  , bgBlueGradient
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
  , cardOverlay
  , sidebarCardOverlay
  , card
  , videoCard
  , sidebarCard
  , embeddedVideoContainer
  , embeddedVideo
  , iconCircle
  , fixedBottomRight
  , funds
  ) where

import Prelude
import Halogen.Css (applyWhen)
import Material.Icons (Icon, iconClass)

-- max-width container
container :: Array String
container = [ "max-w-xl", "mx-auto", "px-4" ]

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
  , "border"
  , "border-transparent"
  , "focus:border-transparent"
  ]

inputBaseFocus :: Array String
inputBaseFocus = inputBase <> [ "focus:ring-1" ]

inputBaseNoFocus :: Array String
inputBaseNoFocus = inputBase <> [ "focus:ring-0" ]

input :: Boolean -> Array String
input valid =
  inputBaseFocus
    <> [ "border-gray" ]
    <> applyWhen (not valid) [ "border-red" ]

inputNoFocus :: Boolean -> Array String
inputNoFocus valid =
  inputBaseNoFocus
    <> [ "border-gray" ]
    <> applyWhen (not valid) [ "border-red" ]

withNestedLabel :: Array String
withNestedLabel = [ "border-gray", "focus:border-gray" ]

inputCard :: Boolean -> Array String
inputCard valid =
  inputBaseFocus
    <> [ "shadow-sm", "focus:shadow", "hover:shadow" ]
    <> if valid then [ "border-transparent" ] else [ "border-red" ]

inputCardNoFocus :: Boolean -> Array String
inputCardNoFocus valid =
  inputBaseNoFocus
    <> [ "shadow-sm", "focus:shadow", "hover:shadow" ]
    <> if valid then [ "border-transparent" ] else [ "border-red" ]

inputError :: Array String
inputError = [ "px-3", "mt-1", "text-red", "text-sm" ]

hasNestedLabel :: Array String
hasNestedLabel = [ "-mt-4" ]

nestedLabel :: Array String
nestedLabel = [ "relative", "z-10", "left-2", "top-2.5", "px-1", "bg-white", "text-xs", "font-semibold" ]

--- cards
cardOverlay :: Boolean -> Array String
cardOverlay visible =
  [ "overflow-hidden"
  , "absolute"
  , "inset-0"
  , "z-20"
  , "flex"
  , "justify-center"
  , "content-end"
  , "md:content-center"
  , "bg-overlay"
  , "transition-opacity"
  , "duration-400"
  ]
    <> if visible then [ "opacity-1" ] else [ "opacity-0", "pointer-events-none" ]

sidebarCardOverlay :: Boolean -> Array String
sidebarCardOverlay visible = cardOverlay visible <> [ "lg:justify-end", "lg:duration-500" ]

cardBase :: Boolean -> Array String
cardBase visible =
  [ "relative" -- this is because (some) cards contain an absoutely positioned close icon
  , "bg-white"
  , "flex-grow"
  , "max-w-sm"
  , "max-h-full"
  , "mx-2"
  , "shadow"
  , "transform"
  , "transition-transform"
  , "duration-400"
  ]
    <> applyWhen (not visible) [ "translate-y-20" ]

card :: Boolean -> Array String
card visible =
  [ "overflow-hidden"
  , "rounded-t"
  , "md:rounded-b"
  , "self-end"
  , "md:self-center"
  ]
    <> cardBase visible

videoCard :: Boolean -> Array String
videoCard visible =
  [ "relative"
  , "lg:max-w-md"
  , "rounded"
  , "self-center"
  ]
    <> cardBase visible

sidebarCard :: Boolean -> Array String
sidebarCard visible =
  [ "overflow-hidden"
  , "rounded-t"
  , "md:rounded-b"
  , "self-end"
  , "md:self-center"
  , "lg:rounded-none"
  , "lg:mx-0"
  , "lg:flex-none"
  , "lg:w-sidebar"
  , "lg:h-full"
  , "lg:justify-self-end"
  , "lg:duration-500"
  ]
    <> cardBase visible
    <> applyWhen (not visible) [ "lg:translate-y-0", "lg:translate-x-80" ]

-- embedded videos
embeddedVideoContainer :: Array String
embeddedVideoContainer = [ "relative", "pb-16:9" ]

embeddedVideo :: Array String
embeddedVideo = [ "absolute", "top-0", "left-0", "w-full", "h-full" ]

--- miscellaneous
iconCircle :: Boolean -> Array String
iconCircle enabled = [ "inline-flex", "items-center", "justify-center", "w-8", "h-8", "rounded-full" ] <> if enabled then bgBlueGradient else [ "bg-lightgray", "text-darkgray" ]

fixedBottomRight :: Array String
fixedBottomRight = [ "absolute", "bottom-4", "right-4" ]

funds :: Array String
funds = [ "text-2xl", "text-purple", "font-semibold" ]
