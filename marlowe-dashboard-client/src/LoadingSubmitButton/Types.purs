module LoadingSubmitButton.Types where

import Data.Either (Either)
import Data.Symbol (SProxy(..))
import Data.Time.Duration (Milliseconds)
import Halogen (RefLabel(..))
import Network.RemoteData (RemoteData)

_submitButtonSlot :: SProxy "submitButtonSlot"
_submitButtonSlot = SProxy

type State
  = { caption :: String
    , styles :: Array String
    , enabled :: Boolean
    , status :: RemoteData String String
    , buttonHeight :: Number
    }

type Input
  = { caption :: String
    , styles :: Array String
    , enabled :: Boolean
    }

data Query a
  = SubmitResult Milliseconds (Either String String) a

data Message
  = OnSubmit
  | OnResultAnimationFinish

data Action
  = Submit
  | OnNewInput Input

buttonRef :: RefLabel
buttonRef = RefLabel "button"
