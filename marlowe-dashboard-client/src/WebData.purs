module WebData (WebData) where

import Network.RemoteData (RemoteData)
import Servant.PureScript.Ajax (AjaxError)

type WebData
  = RemoteData AjaxError
