module Data.Functor(
  Functor(..),
  ($>),
  (<$>),
  (<&>),
  unzip,
  void,
  ) where
import Control.Applicative
import Prelude hiding (unzip)

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
