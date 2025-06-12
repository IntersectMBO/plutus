module Unsafe.Coerce(module Unsafe.Coerce, AnyType) where
import Prelude qualified ()
import Primitives

unsafeCoerce :: forall a b . a -> b
unsafeCoerce = primUnsafeCoerce
