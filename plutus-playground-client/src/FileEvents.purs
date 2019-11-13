module FileEvents
  ( preventDefault
  , readFileFromDragEvent
  ) where

import Data.Either (Either(..))
import Effect (Effect)
import Effect.Aff (Aff, Canceler, Error, makeAff)
import Effect.Uncurried (EffectFn3, runEffectFn3)
import Prelude (Unit, ($), (<<<))
import Web.HTML.Event.DragEvent (DragEvent)

foreign import preventDefault :: DragEvent -> Effect Unit

foreign import _readFileFromDragEvent ::
  EffectFn3
    (String -> Effect Unit)
    (Error -> Effect Unit)
    DragEvent
    Canceler

readFileFromDragEvent :: DragEvent -> Aff String
readFileFromDragEvent event = makeAff $ \callback -> runEffectFn3 _readFileFromDragEvent (callback <<< Right) (callback <<< Left) event
