module Network.StreamData where

import Prelude
import Control.Monad.Error.Class (class MonadError, class MonadThrow)
import Data.Bifunctor (class Bifunctor)
import Data.Bitraversable (class Bifoldable, class Bitraversable, bifoldlDefault, bifoldrDefault, bisequenceDefault)
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Lens (Prism', prism)
import Data.Traversable (class Foldable, class Traversable, foldlDefault, foldrDefault, sequenceDefault)
import Network.RemoteData (RemoteData)
import Network.RemoteData as Remote

data StreamData e a
  = NotAsked
  | Loading
  | Failure e
  | Success a
  | Refreshing a

derive instance genericStreamData :: Generic (StreamData e a) _

derive instance eqStreamData :: (Eq e, Eq a) => Eq (StreamData e a)

derive instance functorStreamData :: Functor (StreamData e)

instance showStreamData :: (Show e, Show a) => Show (StreamData e a) where
  show NotAsked = "StreamData.NotAsked"
  show Loading = "StreamData.Loading"
  show (Failure err) = "StreamData.Failure " <> show err
  show (Success value) = "StreamData.Success " <> show value
  show (Refreshing value) = "StreamData.Refreshing " <> show value

-- | Maps functions to the `Failure` and `Success` values.
instance bifunctorStreamData :: Bifunctor StreamData where
  bimap _ _ NotAsked = NotAsked
  bimap _ _ Loading = Loading
  bimap f _ (Failure err) = Failure (f err)
  bimap _ g (Success value) = Success (g value)
  bimap _ g (Refreshing value) = Refreshing (g value)

-- | If both values are `Success`, the result is `Success`.
-- | If one is `Success` and the other is `Refreshing`, the result is `Refreshing`.
-- | If both are `Refreshing`, the result is `Refreshing`.
-- | If both are `Failure`, the first failure is returned.
instance applyStreamData :: Apply (StreamData e) where
  apply (Success f) (Success value) = Success (f value)
  apply (Refreshing f) (Success value) = Refreshing (f value)
  apply (Success f) (Refreshing value) = Refreshing (f value)
  apply (Refreshing f) (Refreshing value) = Refreshing (f value)
  apply (Failure err) _ = Failure err
  apply _ (Failure err) = Failure err
  apply NotAsked _ = NotAsked
  apply _ NotAsked = NotAsked
  apply Loading _ = Loading
  apply _ Loading = Loading

instance bindStreamData :: Bind (StreamData e) where
  bind NotAsked _ = NotAsked
  bind Loading _ = Loading
  bind (Failure err) _ = (Failure err)
  bind (Success value) f = f value
  bind (Refreshing value) f = f value

instance applicativeStreamData :: Applicative (StreamData e) where
  pure value = Success value

instance monadStreamData :: Monad (StreamData e)

instance monadThrowStreamData :: MonadThrow e (StreamData e) where
  throwError = Failure

instance monadErrorStreamData :: MonadError e (StreamData e) where
  catchError (Failure e) f = f e
  catchError (Success value) _ = Success value
  catchError (Refreshing value) _ = Refreshing value
  catchError NotAsked _ = NotAsked
  catchError Loading _ = Loading

instance foldableStreamData :: Foldable (StreamData e) where
  foldMap f (Success a) = f a
  foldMap f (Refreshing a) = f a
  foldMap _ (Failure e) = mempty
  foldMap _ NotAsked = mempty
  foldMap _ Loading = mempty
  foldr f = foldrDefault f
  foldl f = foldlDefault f

instance traversableStreamData :: Traversable (StreamData e) where
  traverse f (Success a) = Success <$> f a
  traverse f (Refreshing a) = Refreshing <$> f a
  traverse f (Failure e) = pure (Failure e)
  traverse _ NotAsked = pure NotAsked
  traverse _ Loading = pure Loading
  sequence = sequenceDefault

instance bifoldableStreamData :: Bifoldable StreamData where
  bifoldMap _ f (Success a) = f a
  bifoldMap _ f (Refreshing a) = f a
  bifoldMap f _ (Failure e) = f e
  bifoldMap _ _ Loading = mempty
  bifoldMap _ _ NotAsked = mempty
  bifoldr f = bifoldrDefault f
  bifoldl f = bifoldlDefault f

instance bitraversableStreamData :: Bitraversable StreamData where
  bitraverse _ f (Success a) = Success <$> f a
  bitraverse _ f (Refreshing a) = Refreshing <$> f a
  bitraverse f _ (Failure e) = Failure <$> f e
  bitraverse _ _ NotAsked = pure NotAsked
  bitraverse _ _ Loading = pure Loading
  bisequence = bisequenceDefault

------------------------------------------------------------
-- | Convert an `Either` to `StreamData`
fromEither :: forall e a. Either e a -> StreamData e a
fromEither (Left err) = Failure err

fromEither (Right value) = Success value

-- | Modifies any `Success a` to be `Refreshing a`.
refreshing :: forall e a. StreamData e a -> StreamData e a
refreshing (Success a) = Refreshing a

refreshing NotAsked = Loading

refreshing other = other

-- | Modifies any `Refreshing a` to be a `Success a`.
refreshed :: forall e a. StreamData e a -> StreamData e a
refreshed (Refreshing a) = Success a

refreshed other = other

------------------------------------------------------------
-- Prisms & Lenses (oh my!)
_NotAsked :: forall a e. Prism' (StreamData e a) Unit
_NotAsked = prism (const NotAsked) unwrap
  where
  unwrap NotAsked = Right unit

  unwrap y = Left y

_Loading :: forall a e. Prism' (StreamData e a) Unit
_Loading = prism (const Loading) unwrap
  where
  unwrap Loading = Right unit

  unwrap y = Left y

_Failure :: forall a e. Prism' (StreamData e a) e
_Failure = prism Failure unwrap
  where
  unwrap (Failure x) = Right x

  unwrap y = Left y

_Refreshing :: forall a e. Prism' (StreamData e a) a
_Refreshing = prism Refreshing unwrap
  where
  unwrap (Refreshing x) = Right x

  unwrap y = Left y

_Success :: forall a e. Prism' (StreamData e a) a
_Success = prism Success unwrap
  where
  unwrap (Success x) = Right x

  unwrap y = Left y

------------------------------------------------------------
fromRemoteData :: forall e a. RemoteData e a -> StreamData e a
fromRemoteData (Remote.Success a) = Success a

fromRemoteData (Remote.Failure e) = Failure e

fromRemoteData Remote.Loading = Loading

fromRemoteData Remote.NotAsked = NotAsked

toRemoteData :: forall e a. StreamData e a -> RemoteData e a
toRemoteData (Success a) = Remote.Success a

toRemoteData (Refreshing a) = Remote.Success a

toRemoteData (Failure e) = Remote.Failure e

toRemoteData Loading = Remote.Loading

toRemoteData NotAsked = Remote.NotAsked

isAvailable :: forall e a. StreamData e a -> Boolean
isAvailable (Success _) = true

isAvailable (Refreshing _) = true

isAvailable _ = false

isExpected :: forall e a. StreamData e a -> Boolean
isExpected (Refreshing _) = true

isExpected Loading = true

isExpected _ = false
