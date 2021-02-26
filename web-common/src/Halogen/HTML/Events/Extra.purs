module Halogen.HTML.Events.Extra where

import Prelude
import Data.Maybe (Maybe(..))
import Halogen.HTML (IProp)
import Halogen.HTML.Events (onClick, onValueInput)
import Web.Event.Internal.Types (Event)
import Web.UIEvent.MouseEvent (MouseEvent)

onClick_ :: forall a b. b -> IProp ( onClick ∷ MouseEvent | a ) b
onClick_ = onClick <<< const <<< Just

onValueInput_ :: forall a b. (String -> a) -> IProp ( onInput ∷ Event, value ∷ String | b ) a
onValueInput_ a = onValueInput $ Just <<< a
