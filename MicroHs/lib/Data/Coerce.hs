module Data.Coerce(Coercible, coerce) where
import Prelude qualified ()
import Primitives

type Coercible :: forall k . k -> k -> Constraint
class Coercible a b

coerce :: forall a b . Coercible a b => a -> b
coerce = primUnsafeCoerce
