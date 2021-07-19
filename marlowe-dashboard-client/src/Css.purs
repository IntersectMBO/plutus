module Css
  ( maxWidthContainer
  , bgBlueGradient
  , button
  , withAnimation
  , withIcon
  , withShadow
  , primaryButton
  , secondaryButton
  , whiteButton
  , input
  , inputNoFocus
  , inputNoBorder
  , pseudoDropdown
  , unstyledInput
  , inputError
  , hasNestedLabel
  , nestedLabel
  , cardOverlay
  , sidebarCardOverlay
  , card
  , videoCard
  , sidebarCard
  , cardHeader
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
maxWidthContainer :: Array String
maxWidthContainer = [ "max-w-xl", "mx-auto", "px-4" ]

--- color gradients
bgBlueGradient :: Array String
bgBlueGradient = [ "bg-gradient-to-r", "from-purple", "to-lightpurple", "text-white" ]

-- buttons
button :: Array String
button =
  [ "px-6"
  , "py-4"
  , "rounded-full"
  , "leading-none"
  , "whitespace-nowrap"
  , "outline-none"
  , "select-none"
  , "focus:outline-none"
  , "disabled:bg-none"
  , "disabled:bg-lightgray"
  , "disabled:text-darkgray"
  , "disabled:shadow-none"
  ]

withShadow :: Array String
withShadow = [ "shadow", "hover:shadow-lg" ]

withAnimation :: Array String
withAnimation = [ "transition-all", "duration-200" ]

primaryButton :: Array String
primaryButton = button <> bgBlueGradient <> withShadow <> withAnimation <> [ "font-bold" ]

secondaryButton :: Array String
secondaryButton = button <> withAnimation <> [ "font-bold", "bg-lightgray", "text-black", "hover:shadow" ]

whiteButton :: Array String
whiteButton = button <> withShadow <> withAnimation <> [ "font-bold", "bg-white" ]

withIcon :: Icon -> Array String
withIcon icon = [ "with-icon", "with-icon-" <> iconClass icon ]

--- inputs
inputBase :: Array String
inputBase =
  [ "block"
  , "w-full"
  , "p-4"
  , "rounded-sm"
  , "leading-none"
  , "outline-none"
  , "focus:outline-none"
  , "text-black"
  , "border-2"
  ]
    <> withAnimation

-- note we set rings on focus-within as well as focus, so that we can use these classes on divs
-- with unstyled inputs inside them, making that whole parent div look like the input
input :: Boolean -> Array String
input valid =
  inputBase
    <> [ "focus:border-transparent", "focus-within:border-transparent", "focus:ring-2", "focus-within:ring-2" ]
    <> if valid then [ "border-gray", "focus:ring-purple", "focus-within:ring-purple" ] else [ "border-red", "focus:ring-red", "focus-within:ring-red" ]

-- use this on pseudo select elements, because the focus ring doesn't play well with the dropdown
inputNoFocus :: Boolean -> Array String
inputNoFocus valid =
  inputBase
    <> [ "focus:ring-0", "focus:border-gray" ]
    <> if valid then [ "border-gray" ] else [ "border-red" ]

inputNoBorder :: Array String
inputNoBorder =
  [ "block"
  , "w-full"
  , "p-2"
  , "rounded"
  , "transition-all"
  , "duration-200"
  , "outline-none"
  , "focus:outline-none"
  , "text-black"
  , "border-0"
  ]

pseudoDropdown :: Boolean -> Array String
pseudoDropdown open =
  [ "absolute"
  , "z-20"
  , "w-full"
  , "max-h-56"
  , "overflow-x-hidden"
  , "overflow-y-auto"
  , "-mt-2"
  , "pt-2"
  , "border-b-2"
  , "border-l-2"
  , "border-r-2"
  , "border-gray"
  , "bg-white"
  , "shadow"
  , "rounded-b-sm"
  ]
    <> withAnimation
    <> if open then [ "opacity-100" ] else [ "hidden", "opacity-0" ]

-- use this on an input inside a div styled like an input
unstyledInput :: Array String
unstyledInput = [ "leading-none", "p-0", "border-0", "focus:ring-0" ]

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
  , "lg:rounded-b"
  , "self-end"
  , "lg:self-center"
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
  , "self-end"
  , "h-90pc"
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

cardHeader :: Array String
cardHeader = [ "text-lg", "font-semibold", "leading-none", "px-4", "py-4.5", "border-gray", "border-b" ]

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
