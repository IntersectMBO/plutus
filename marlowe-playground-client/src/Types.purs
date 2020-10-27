module Types where

import Network.RemoteData (RemoteData)
import Servant.PureScript.Ajax (AjaxError)

type WebData
  = RemoteData AjaxError

data MarloweError
  = MarloweError String
