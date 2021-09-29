module Component.Button.View (button) where

import Prologue
import Component.Button.Types (Variant(..))
import Data.Array (length)
import Data.Maybe (isNothing)
import Halogen.Css (classNames)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

button ::
  forall w action.
  Variant ->
  Maybe action ->
  Array String ->
  Array (HH.HTML w action) ->
  HH.HTML w action
button variant onClick extraClasses children =
  HH.button
    [ classNames $ classes <> extraClasses
    , HP.disabled disabled
    , HE.onClick (const onClick)
    ]
    children
  where
  disabled = isNothing onClick

  classes =
    [ "rounded-full"
    , "flex"
    , "font-bold"
    , "p-4"
    , if disabled then "cursor-default" else "cursor-pointer"
    , if length children == 1 then "justify-center" else "justify-between"
    , "transition-all"
    , "duration-200"
    ]
      <> variantStyles

  -- TODO make the focus and active styles better
  variantStyles
    | disabled = [ "bg-gray-200", "text-black", "text-opacity-50" ]
    | otherwise = case variant of
      Primary -> [ "bg-gradient-to-r", "from-purple", "to-lightpurple", "text-white", "shadow", "active:shadow", "hover:shadow-lg" ]
      Secondary -> [ "bg-gray-200", "text-black", "hover:shadow", "active:shadow-none" ]
