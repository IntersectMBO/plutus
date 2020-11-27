module Blockly.Events where

import Data.Maybe (Maybe(..))
import Data.Function.Uncurried (Fn4, runFn4)

unsafeReadBlocklyEventType :: forall a b. String -> a -> Maybe b
unsafeReadBlocklyEventType name value = runFn4 _unsafeReadBlocklyEventType Nothing Just name value

foreign import _unsafeReadBlocklyEventType ::
  forall a b.
  Fn4
    (forall x. Maybe x)
    (forall x. x -> Maybe x)
    String
    a
    (Maybe b)
