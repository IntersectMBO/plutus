module Data.Functor(
  Functor(..),
  ($>),
  (<$>),
  (<&>),
  unzip,
  void,
  ) where
import Data.Function
import Prelude qualified ()
import Primitives

infixl 4 <$

class Functor f where
  fmap :: forall a b . (a -> b) -> f a -> f b
  (<$) :: forall a b . a -> f b -> f a
  (<$) =  fmap . const

infixl 4 <$>
(<$>) :: forall f a b . Functor f => (a -> b) -> f a -> f b
(<$>) = fmap

infixl 1 <&>
(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip (<$>)

infixl 4 $>
($>) :: Functor f => f a -> b -> f b
($>) = flip (<$)

unzip :: Functor f => f (a, b) -> (f a, f b)
unzip xs = ( (\(a,_)->a) <$> xs,
             (\(_,b)->b) <$> xs )

void :: forall f a . Functor f => f a -> f ()
void = fmap (const ())
