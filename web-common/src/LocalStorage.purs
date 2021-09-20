module LocalStorage
  ( setItem
  , removeItem
  , getItem
  , listen
  , getItems
  , Key(Key)
  , RawStorageEvent
  ) where

import Prelude
import Control.Coroutine (Producer, producer)
import Data.Either (Either(..))
import Data.Function.Uncurried (Fn3, mkFn3)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.Nullable (Nullable, toMaybe)
import Effect (Effect)
import Effect.Aff (Aff, Canceler, effectCanceler, makeAff)
import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn1, runEffectFn2)

newtype Key
  = Key String

derive instance genericKey :: Generic Key _

derive instance newtypeKey :: Newtype Key _

instance semigroupKey :: Semigroup Key where
  append (Key a) (Key b) = Key (append a b)

instance showKey :: Show Key where
  show = genericShow

newtype RawStorageEvent
  = RawStorageEvent
  { key :: Maybe Key
  , oldValue :: Maybe String
  , newValue :: Maybe String
  }

derive instance genericRawStorageEvent :: Generic RawStorageEvent _

derive instance newtypeRawStorageEvent :: Newtype RawStorageEvent _

instance showRawStorageEvent :: Show RawStorageEvent where
  show = genericShow

toEvent :: Nullable String -> Nullable String -> Nullable String -> RawStorageEvent
toEvent key oldValue newValue =
  RawStorageEvent
    { key: Key <$> toMaybe key
    , oldValue: toMaybe oldValue
    , newValue: toMaybe newValue
    }

------------------------------------------------------------
foreign import _setItem :: EffectFn2 Key String Unit

foreign import _removeItem :: EffectFn1 Key Unit

foreign import _getItem :: EffectFn1 Key (Nullable String)

foreign import _listen ::
  EffectFn2
    (Fn3 (Nullable String) (Nullable String) (Nullable String) RawStorageEvent)
    (RawStorageEvent -> Effect Unit)
    (EffectFn1 Unit Unit)

foreign import _getItems ::
  EffectFn1
    (Fn3 (Nullable String) (Nullable String) (Nullable String) RawStorageEvent)
    (Array RawStorageEvent)

setItem :: Key -> String -> Effect Unit
setItem = runEffectFn2 _setItem

removeItem :: Key -> Effect Unit
removeItem = runEffectFn1 _removeItem

getItem :: Key -> Effect (Maybe String)
getItem = map toMaybe <$> runEffectFn1 _getItem

listen :: Producer RawStorageEvent Aff Unit
listen =
  producer
    $ makeAff \callback -> do
        canceller <- runEffectFn2 _listen (mkFn3 toEvent) (callback <<< Right <<< Left)
        pure $ effectCanceler $ runEffectFn1 canceller unit

getItems :: Effect (Array RawStorageEvent)
getItems = runEffectFn1 _getItems (mkFn3 toEvent)
