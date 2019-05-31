module LocalStorage
  ( Key
      ( Key
      )
  , RawStorageEvent
  , getItem
  , getItems
  , listen
  , setItem
  ) where

import Control.Coroutine (Producer, producer)
import Effect.Aff (Aff, Canceler, makeAff)
import Effect (Effect)
import Data.Either (Either(..))
import Data.Function.Uncurried (Fn1, Fn2, Fn3, mkFn3, runFn1, runFn2)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.Nullable (Nullable, toMaybe)
import Prelude (class Show, Unit, map, (<$>), (<<<))

newtype Key
  = Key String

derive instance genericKey ::
  Generic Key _

derive instance newtypeKey ::
  Newtype Key _

instance showKey ::
  Show Key where
    show = genericShow

newtype RawStorageEvent
  = RawStorageEvent {key :: Maybe Key, oldValue :: Maybe String, newValue :: Maybe String}

derive instance genericRawStorageEvent ::
  Generic RawStorageEvent _

derive instance newtypeRawStorageEvent ::
  Newtype RawStorageEvent _

instance showRawStorageEvent ::
  Show RawStorageEvent where
    show = genericShow

toEvent ::
  Nullable String ->
  Nullable String ->
  Nullable String ->
  RawStorageEvent
toEvent key oldValue newValue = RawStorageEvent { key: Key <$> toMaybe key
                                                , oldValue: toMaybe oldValue
                                                , newValue: toMaybe newValue
                                                }

------------------------------------------------------------
foreign import _setItem ::
  Fn2 Key String (Effect Unit)

foreign import _getItem ::
  Fn1 Key (Effect (Nullable String))

foreign import _listen ::
  Fn2 (Fn3 (Nullable String) (Nullable String) (Nullable String) RawStorageEvent) (RawStorageEvent -> Effect Unit) (Effect Canceler)

foreign import _getItems ::
  Fn1 (Fn3 (Nullable String) (Nullable String) (Nullable String) RawStorageEvent) (Effect (Array RawStorageEvent))

setItem ::
  Key ->
  String ->
  Effect Unit
setItem = runFn2 _setItem

getItem ::
  Key ->
  Effect (Maybe String)
getItem = map toMaybe <$> runFn1 _getItem

listen ::
  Producer RawStorageEvent Aff Unit
listen = producer (makeAff \callback ->
  runFn2 _listen (mkFn3 toEvent) (callback <<< Right <<< Left))

getItems ::
  Effect (Array RawStorageEvent)
getItems = runFn1 _getItems (mkFn3 toEvent)
