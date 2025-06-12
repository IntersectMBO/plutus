-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Maybe(module Data.Maybe, module Data.Maybe_Type) where
import qualified Prelude()              -- do not import Prelude
import Primitives
import Control.Applicative
import Control.Error
import Control.Monad
import Control.Monad.Fail
import Data.Bool
import Data.Char
import Data.Eq
import Data.Function
import Data.Functor
import Data.Int
import Data.List
import Data.Maybe_Type
import Data.Monoid.Internal
import Data.Ord
import Text.Show

instance Eq a => Eq (Maybe a) where
  Nothing == Nothing  =  True
  Just x  == Just x'  =  x == x'
  _       == _        =  False

instance Ord a => Ord (Maybe a) where
  Nothing `compare` Nothing = EQ
  Nothing `compare` Just _  = LT
  Just _  `compare` Nothing = GT
  Just x  `compare` Just y  = x `compare` y

instance (Show a) => Show (Maybe a) where
  showsPrec _ Nothing  = showString "Nothing"
  showsPrec p (Just a) = showParen (p >= 11) (showString "Just " . showsPrec 11 a)

instance Functor Maybe where
  fmap _ Nothing  = Nothing
  fmap f (Just a) = Just (f a)

instance Applicative Maybe where
  pure = Just
  Just f <*> Just a = Just (f a)
  _      <*> _      = Nothing

instance Monad Maybe where
  return = pure
  Nothing >>= _ = Nothing
  Just a  >>= f = f a

instance MonadFail Maybe where
  fail _ = Nothing

instance MonadPlus Maybe where
  mzero = Nothing
  Nothing `mplus` y = y
  x       `mplus` _ = x

instance Alternative Maybe where
  empty = Nothing
  Nothing <|> y = y
  x       <|> _ = x

instance Semigroup a => Semigroup (Maybe a) where
  Nothing <> b       = b
  a       <> Nothing = a
  Just a  <> Just b  = Just (a <> b)

instance Semigroup a => Monoid (Maybe a) where
  mempty = Nothing

maybe :: forall a r . r -> (a -> r) -> Maybe a -> r
maybe r _ Nothing = r
maybe _ f (Just a) = f a

fromMaybe :: forall a . a -> Maybe a -> a
fromMaybe a Nothing = a
fromMaybe _ (Just a) = a

fromJust :: forall a . Maybe a -> a
fromJust Nothing = error "fromJust: Nothing"
fromJust (Just a) = a

catMaybes :: forall a . [Maybe a] -> [a]
catMaybes mxs = [ x | Just x <- mxs ]

isJust :: forall a . Maybe a -> Bool
isJust Nothing = False
isJust (Just _) = True

isNothing :: forall a . Maybe a -> Bool
isNothing Nothing = True
isNothing (Just _) = False

mapMaybe :: forall a b . (a -> Maybe b) -> [a] -> [b]
mapMaybe _ [] = []
mapMaybe f (a:as) =
  case f a of
    Nothing -> mapMaybe f as
    Just b -> b : mapMaybe f as

maybeToList :: forall a . Maybe a -> [a]
maybeToList Nothing = []
maybeToList (Just a) = [a]

listToMaybe :: forall a . [a] -> Maybe a
listToMaybe [] = Nothing
listToMaybe (a:_) = Just a
