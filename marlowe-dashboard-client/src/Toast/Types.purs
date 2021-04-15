module Toast.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import Data.Maybe (Maybe(..))
import Halogen (SubscriptionId)
import Material.Icons (Icon(..))

type ToastMessage
  = { shortDescription :: String
    , longDescription :: Maybe String
    , icon :: Icon
    , iconColor :: String
    , textColor :: String
    , bgColor :: String
    , timeout :: Number
    }

data Action
  = AddToast ToastMessage
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
type ToastState
  = { message :: ToastMessage
    , expanded :: Boolean
    , timeoutSubscription :: SubscriptionId
    }

type State
  = { mToast :: Maybe ToastState
    }

successToast :: String -> ToastMessage
successToast shortDescription =
  { shortDescription
  , longDescription: Nothing
  , icon: DoneWithCircle
  , iconColor: "text-lightgreen"
  , textColor: "text-white"
  , bgColor: "bg-black"
  , timeout: 2500.0
  }

errorToast :: String -> Maybe String -> ToastMessage
errorToast shortDescription longDescription =
  { shortDescription
  , longDescription
  , icon: ErrorOutline
  , iconColor: "text-white"
  , textColor: "text-white"
  , bgColor: "bg-red"
  , timeout: 5000.0
  }

connectivityErrorToast :: String -> ToastMessage
connectivityErrorToast shortDescription = errorToast shortDescription (Just "There was a problem connecting with the server, please contact support if this problem persists.")
