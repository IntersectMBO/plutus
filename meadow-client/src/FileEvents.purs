module FileEvents
  ( FILE
  , preventDefault
  , readFileFromDragEvent
  ) where

import Control.Monad.Aff
  ( Aff
  , Canceler
  , Error
  , makeAff
  )
import Control.Monad.Eff
  ( Eff
  , kind Effect
  )
import DOM.HTML.Event.Types
  ( DragEvent
  )
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

foreign import preventDefault ::
  forall eff.
  DragEvent ->
  Eff eff Unit

foreign import data FILE ::
  Effect

foreign import _readFileFromDragEvent ::
  forall eff.
  Fn3 (String -> Eff (file :: FILE | eff) Unit) (Error -> Eff (file :: FILE | eff) Unit) DragEvent (Eff (file :: FILE | eff) (Canceler (file :: FILE | eff)))

readFileFromDragEvent ::
  forall aff.
  DragEvent ->
  Aff (file :: FILE | aff) String
readFileFromDragEvent event = makeAff $ \callback ->
  runFn3 _readFileFromDragEvent (callback <<< Right) (callback <<< Left) event
