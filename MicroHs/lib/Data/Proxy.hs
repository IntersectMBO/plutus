module Data.Proxy(module Data.Proxy) where
import Data.Bool_Type
import Data.Eq
import Data.Functor
import Prelude qualified ()
import Primitives
import Text.Show

type Proxy :: forall (k::Kind) . k -> Type
data Proxy a = Proxy

instance Show (Proxy a) where
  show _ = "Proxy"

instance Eq (Proxy a) where
  _ == _  =  True

instance Functor Proxy where
  fmap _ Proxy = Proxy
