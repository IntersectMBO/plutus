module Data.Functor.Foldable where

import AjaxUtils (defaultJsonOptions)
import Data.Eq (class Eq, class Eq1)
import Data.Functor (class Functor)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Newtype (class Newtype)
import Data.Show (class Show)
import Foreign.Generic (genericDecode, genericEncode)
import Foreign.Generic.Class (class Decode, class Encode)
import Matryoshka (class Corecursive, class Recursive)
import Schema (FormArgumentF)

-- | This recursive type is isomorphic to `Data.Functor.Mu.Mu`, and
-- only exists because we want `Encode`/`Decode` instances.
newtype Fix f
  = Fix (f (Fix f))

derive instance newtypeFix :: Newtype (Fix f) _

derive instance genericFix :: Generic (Fix f) _

derive instance eqFix :: Eq1 f => Eq (Fix f)

instance recursiveFix ∷ Functor f ⇒ Recursive (Fix f) f where
  project (Fix v) = v

instance corecursiveFix ∷ Functor f ⇒ Corecursive (Fix f) f where
  embed v = Fix v

------------------------------------------------------------
instance encodeFix :: Encode (Fix FormArgumentF) where
  encode (Fix value) = genericEncode defaultJsonOptions value

instance decodeFix :: Decode (Fix FormArgumentF) where
  decode value = genericDecode defaultJsonOptions value

--
instance showFix :: Show (Fix FormArgumentF) where
  show value = genericShow value
