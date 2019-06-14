module Fix where

import Data.Functor (class Functor)
import Data.Traversable (class Traversable)
import Foreign (Foreign)
import Foreign.Class (class Decode, class Encode, decode, encode)
import Matryoshka (class Corecursive, class Recursive, anaM, cata)

newtype Fix f = In (f (Fix f))

unroll :: forall f. Fix f -> f (Fix f)
unroll (In x) = x

roll :: forall f. f (Fix f) -> Fix f
roll x = (In x)

instance recursiveFix ∷ Functor f => Recursive (Fix f) f where
  project = unroll

instance corecursiveFix ∷ Functor f => Corecursive (Fix f) f where
  embed = roll

instance encodeFix :: (Encode (f Foreign), Functor f) => Encode (Fix f) where
  encode value = cata encode value

instance decodeFix :: (Decode (f Foreign), Traversable f) => Decode (Fix f) where
  decode value = anaM decode value
