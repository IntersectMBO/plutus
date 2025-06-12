module Data.TypeLits(
  Symbol,
  Nat,
  KnownNat(..),
  KnownSymbol(..),
  ) where
import Data.Char_Type
import Data.Integer
import Prelude qualified ()
import Primitives

class KnownNat (n :: Nat) where
  natVal :: forall (proxy :: Nat -> Type) . proxy n -> Integer

class KnownSymbol (s :: Symbol) where
  symbolVal :: forall (proxy :: Symbol -> Type) . proxy s -> String
