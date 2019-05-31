module FileEvents
  ( preventDefault
  , readFileFromDragEvent
  ) where

import Effect.Aff
  ( Aff
  , Canceler
  , Error
  , makeAff
  )
import Effect
  ( Effect
  )
import Web.HTML.Event.DragEvent (DragEvent)
import Data.Either
  ( Either(..)
  )
import Data.Function.Uncurried
  ( Fn3
  , runFn3
  )
import Prelude
  ( Unit
  , ($)
  , (<<<)
  )

foreign import preventDefault :: DragEvent -> Effect Unit

foreign import _readFileFromDragEvent ::
  Fn3 (String -> Effect Unit) (Error -> Effect Unit) DragEvent (Effect Canceler)

readFileFromDragEvent :: DragEvent -> Aff String
readFileFromDragEvent event = makeAff $ \callback ->
  runFn3 _readFileFromDragEvent (callback <<< Right) (callback <<< Left) event
