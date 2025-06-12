module Data.Records(
  module Data.Proxy,
  HasField(..),
  SetField(..),
  hasField,
  composeSet,
  ) where
import Data.Function
import Data.Proxy
import Prelude qualified ()
import Primitives

type Get r a = r -> a
type Set r a = r -> a -> r
type GetSet r a = r -> (a, a -> r)

type  HasField :: forall (k::Kind) . k -> Type -> Type -> Constraint
class HasField x r a | x r -> a where
  getField :: Proxy x -> r -> a -- Get r a

type  SetField :: forall (k::Kind) . k -> Type -> Type -> Constraint
class SetField x r a | x r -> a where
  setField :: Proxy x -> r -> a -> r -- Set r a

hasField :: forall x r a . (HasField x r a, SetField x r a) => Proxy x -> r -> (a, a -> r)                    -- GetSet r a
hasField p r = (getField p r, setField p r)

composeSet :: forall a b c . GetSet a b -> (b -> c -> b) -> (a -> c -> a)
composeSet gs1 b_to_c_to_b a c =
  case gs1 a of
    (b, b_to_a) -> b_to_a (b_to_c_to_b b c)
