module Web.Event.Extra
  ( class IsEvent
  , toEvent
  , preventDefault
  , readFileFromDragEvent
  ) where

import Data.Either (Either(..))
import Effect (Effect)
import Effect.Aff (Aff, Canceler, Error, makeAff)
import Effect.Uncurried (EffectFn3, runEffectFn3)
import Prelude (Unit, ($), (<<<))
import Web.Event.Event (Event)
import Web.Event.Event (preventDefault) as WebEvent
import Web.HTML.Event.DragEvent (DragEvent)
import Web.HTML.Event.DragEvent (toEvent) as DragEvent
import Web.UIEvent.FocusEvent (FocusEvent)
import Web.UIEvent.FocusEvent (toEvent) as FocusEvent
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Web.UIEvent.KeyboardEvent (toEvent) as KeyboardEvent
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.MouseEvent (toEvent) as MouseEvent

class IsEvent e where
  toEvent :: e -> Event

instance eventIsEvent :: IsEvent Event where
  toEvent event = event

instance dragEventIsEvent :: IsEvent DragEvent where
  toEvent = DragEvent.toEvent

instance focusEventIsEvent :: IsEvent FocusEvent where
  toEvent = FocusEvent.toEvent

instance keyboardEventIsEvent :: IsEvent KeyboardEvent where
  toEvent = KeyboardEvent.toEvent

instance mouseEventIsEvent :: IsEvent MouseEvent where
  toEvent = MouseEvent.toEvent

preventDefault :: forall e. IsEvent e => e -> Effect Unit
preventDefault = WebEvent.preventDefault <<< toEvent

foreign import _readFileFromDragEvent ::
  EffectFn3
    (String -> Effect Unit)
    (Error -> Effect Unit)
    DragEvent
    Canceler

readFileFromDragEvent :: DragEvent -> Aff String
readFileFromDragEvent event = makeAff $ \callback -> runEffectFn3 _readFileFromDragEvent (callback <<< Right) (callback <<< Left) event
