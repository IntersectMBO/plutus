module Toast.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import Data.Maybe (Maybe(..))
import Material.Icons (Icon(..))

type Toast
  = { shortDescription :: String
    , longDescription :: Maybe String
    , icon :: Icon
    , iconColor :: String
    , textColor :: String
    , bgColor :: String
    , timeout :: Number
    }

data Action
  = AddToast Toast
  | ExpandToast
  | CloseToast
  | ToastTimeout

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "Toast." <> s

instance actionIsEvent :: IsEvent Action where
  toEvent (AddToast _) = Just $ defaultEvent "AddToast"
  toEvent ExpandToast = Just $ defaultEvent "ExpandToast"
  toEvent CloseToast = Just $ defaultEvent "CloseToast"
  toEvent ToastTimeout = Just $ defaultEvent "ToastTimeout"

-- TODO: For now the state and actions can only represent a single toast. If you open a new toast
--       it will replace the current one. We could later on extend this to have multiple messages
-- FIXME: Add subscription id and put all three under a Maybe
type State
  = { mToast :: Maybe Toast
    , expanded :: Boolean
    }

successToast :: String -> Toast
successToast shortDescription =
  { shortDescription
  , longDescription: Nothing
  , icon: DoneWithCircle
  , iconColor: "text-lightgreen"
  , textColor: "text-white"
  , bgColor: "bg-black"
  , timeout: 3500.0
  }

errorToast :: String -> Maybe String -> Toast
errorToast shortDescription longDescription =
  { shortDescription
  , longDescription
  , icon: ErrorOutline
  , iconColor: "text-white"
  , textColor: "text-white"
  , bgColor: "bg-red"
  , timeout: 10000.0
  }
