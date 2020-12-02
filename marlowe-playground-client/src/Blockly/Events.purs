module Blockly.Events where

import Data.Maybe (Maybe(..))
import Data.Function.Uncurried (Fn4, runFn4)

-- This function let us check if a blockly event is of the desired type. It was inspired by unsafeReadProtoTagged
-- and the reason it's unsafe, it's because there could be other objects that have a property called `type` with
-- the appropiate value, but may not have the correct shape.
-- https://pursuit.purescript.org/packages/purescript-web-events/2.0.1/docs/Web.Internal.FFI#v:unsafeReadProtoTagged
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

-- Similar to the above, this function expects to receive a Blockly event and a property that may be undefined
-- for example "newParentId" and return the property in a maybe
unsafePropertyMaybeUndefined :: forall a b. String -> a -> Maybe b
unsafePropertyMaybeUndefined property event = runFn4 _unsafePropertyMaybeUndefined Nothing Just property event

foreign import _unsafePropertyMaybeUndefined ::
  forall a b.
  Fn4
    (forall x. Maybe x)
    (forall x. x -> Maybe x)
    String
    a
    (Maybe b)
