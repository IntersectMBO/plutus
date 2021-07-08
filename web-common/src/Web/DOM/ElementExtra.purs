module Web.Dom.ElementExtra
  ( ScrollBehavior(..)
  , Alignment(..)
  , scrollTo
  , scrollIntoView
  , throttledOnScroll
  , debouncedOnScroll
  ) where

import Prelude
import Effect (Effect)
import Web.DOM (Element)

data ScrollBehavior
  = Smooth
  | Auto

scrollBehaviorToFFI :: ScrollBehavior -> String
scrollBehaviorToFFI Smooth = "smooth"

scrollBehaviorToFFI Auto = "auto"

data Alignment
  = Start
  | Center
  | End
  | Nearest

alignmentToFFI :: Alignment -> String
alignmentToFFI Start = "start"

alignmentToFFI Center = "center"

alignmentToFFI End = "end"

alignmentToFFI Nearest = "nearest"

foreign import _scrollTo :: { left :: Number, top :: Number, behavior :: String } -> Element -> Effect Unit

scrollTo :: ScrollBehavior -> { left :: Number, top :: Number } -> Element -> Effect Unit
scrollTo behavior { left, top } = _scrollTo { left, top, behavior: scrollBehaviorToFFI behavior }

foreign import _scrollIntoView :: { block :: String, inline :: String, behavior :: String } -> Element -> Effect Unit

scrollIntoView :: { block :: Alignment, inline :: Alignment, behavior :: ScrollBehavior } -> Element -> Effect Unit
scrollIntoView { block, inline, behavior } =
  _scrollIntoView
    { block: alignmentToFFI block
    , inline: alignmentToFFI inline
    , behavior: scrollBehaviorToFFI behavior
    }

foreign import throttledOnScroll :: Number -> Element -> ({ left :: Number, top :: Number } -> Effect Unit) -> Effect (Effect Unit)

foreign import debouncedOnScroll :: Number -> Element -> ({ left :: Number, top :: Number } -> Effect Unit) -> Effect (Effect Unit)
