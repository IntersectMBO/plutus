module LocalStorage
       ( setItem
       , getItem
       , listen
       , getItems
       , Key(Key)
       , LOCALSTORAGE
       , RawStorageEvent
       )
       where

import Control.Coroutine (Producer, producer)
import Control.Monad.Aff (Aff, Canceler, makeAff)
import Control.Monad.Eff (Eff, kind Effect)
import Data.Either (Either(..))
import Data.Function.Uncurried (Fn1, Fn2, Fn3, mkFn3, runFn1, runFn2)
import Data.Generic (class Generic, gShow)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.Nullable (Nullable, toMaybe)
import Prelude (class Show, Unit, map, (<$>), (<<<))

foreign import data LOCALSTORAGE :: Effect

newtype Key = Key String

derive instance genericKey :: Generic Key
derive instance newtypeKey :: Newtype Key _

instance showKey :: Show Key where
  show = gShow

newtype RawStorageEvent = RawStorageEvent
  { key :: Maybe Key
  , oldValue :: Maybe String
  , newValue :: Maybe String
  }

derive instance genericRawStorageEvent :: Generic RawStorageEvent
derive instance newtypeRawStorageEvent :: Newtype RawStorageEvent _

instance showRawStorageEvent :: Show RawStorageEvent where
  show = gShow

toEvent :: Nullable String -> Nullable String -> Nullable String -> RawStorageEvent
toEvent key oldValue newValue = RawStorageEvent
  { key: Key <$> toMaybe key
  , oldValue: toMaybe oldValue
  , newValue: toMaybe newValue
  }

------------------------------------------------------------

foreign import _setItem :: forall eff. Fn2 Key String (Eff (localStorage :: LOCALSTORAGE | eff) Unit)
foreign import _getItem :: forall eff. Fn1 Key (Eff (localStorage :: LOCALSTORAGE | eff) (Nullable String))
foreign import _listen ::
  forall eff.
    Fn2
      (Fn3 (Nullable String) (Nullable String) (Nullable String) RawStorageEvent)
      (RawStorageEvent -> Eff (localStorage :: LOCALSTORAGE | eff) Unit)
      (Eff (localStorage :: LOCALSTORAGE | eff) (Canceler (localStorage :: LOCALSTORAGE | eff)))

foreign import _getItems ::
  forall eff.
    Fn1
      (Fn3 (Nullable String) (Nullable String) (Nullable String) RawStorageEvent)
      (Eff (localStorage :: LOCALSTORAGE | eff) (Array RawStorageEvent))

setItem :: forall eff. Key -> String -> Eff (localStorage :: LOCALSTORAGE | eff) Unit
setItem = runFn2 _setItem

getItem :: forall eff. Key -> Eff (localStorage :: LOCALSTORAGE | eff) (Maybe String)
getItem = map toMaybe <$> runFn1 _getItem

listen :: forall aff. Producer RawStorageEvent (Aff (localStorage :: LOCALSTORAGE | aff)) Unit
listen =
  producer (makeAff \callback -> runFn2 _listen (mkFn3 toEvent) (callback <<< Right <<< Left))

getItems :: forall eff. Eff (localStorage :: LOCALSTORAGE | eff) (Array RawStorageEvent)
getItems = runFn1 _getItems (mkFn3 toEvent)
