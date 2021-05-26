module Halogen.HTML.Events.Extra where

import Prelude
import Data.Maybe (Maybe(..))
import Halogen.HTML (IProp)
import Halogen.HTML.Events (onBlur, onClick, onFocus, onValueInput)
import Web.Event.Internal.Types (Event)
import Web.UIEvent.FocusEvent (FocusEvent)
import Web.UIEvent.MouseEvent (MouseEvent)

onClick_ :: forall a b. a -> IProp ( onClick :: MouseEvent | b ) a
onClick_ = onClick <<< const <<< Just

onValueInput_ :: forall a b. (String -> a) -> IProp ( onInput :: Event, value :: String | b ) a
onValueInput_ a = onValueInput $ Just <<< a

onFocus_ :: forall a b. a -> IProp ( onFocus :: FocusEvent | b ) a
onFocus_ = onFocus <<< const <<< Just

onBlur_ :: forall a b. a -> IProp ( onBlur :: FocusEvent | b ) a
onBlur_ = onBlur <<< const <<< Just
