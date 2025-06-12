module Control.Applicative(
  Applicative(..),
  (<$>), (<$), (<**>),
  liftA, liftA3,
  Alternative(..),
  guard, asum, optional,
  module Data.Functor.Const_Type,
  ) where
import Data.Bool_Type
import Data.Function
import Data.Functor
import Data.Functor.Const_Type
import Data.List_Type
import Data.Maybe_Type
import Prelude qualified ()
import Primitives

infixl 4 <*>, *>, <*, <**>

class Functor f => Applicative f where
  pure        :: forall a . a -> f a
  (<*>)       :: forall a b . f (a -> b) -> f a -> f b
  (*>)        :: forall a b . f a -> f b -> f b
  (<*)        :: forall a b . f a -> f b -> f a
  liftA2      :: forall a b c . (a -> b -> c) -> f a -> f b -> f c
  (<*>)        = liftA2 id
  a1 *> a2     = (id <$ a1) <*> a2
  a1 <* a2     = const <$> a1 <*> a2
  liftA2 f a b = f <$> a <*> b

liftA :: forall f a b . Applicative f => (a -> b) -> f a -> f b
liftA f a = f <$> a

liftA3 :: forall f a b c d . Applicative f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftA3 f a b c = f <$> a <*> b <*> c

(<**>) :: forall f a b . Applicative f => f a -> f (a -> b) -> f b
(<**>) = liftA2 (\ a f -> f a)

-------------------------------------------------------

infixl 3 <|>

class Applicative f => Alternative f where
    empty :: forall a . f a
    (<|>) :: forall a . f a -> f a -> f a

    some :: forall a . f a -> f [a]
    some a = (:) <$> a <*> many a

    many :: forall a . f a -> f [a]
    many a = some a <|> pure []

guard :: forall f a . Alternative f => Bool -> f ()
guard b = if b then pure () else empty

asum :: forall f a . Alternative f => [f a] -> f a
asum []     = empty
asum (a:as) = a <|> asum as

optional :: forall f a . Alternative f => f a -> f (Maybe a)
optional a = Just <$> a <|> pure Nothing
