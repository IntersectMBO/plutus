module Types
  ( AjaxResponse
  , DecodedAjaxResponse
  , WebData
  , DecodedWebData
  , DecodedAjaxError
  ) where

import Data.Either (Either)
import Foreign (MultipleErrors)
import Network.RemoteData (RemoteData)
import Servant.PureScript.Ajax (AjaxError)

type AjaxResponse
  = Either AjaxError

type DecodedAjaxResponse
  = Either DecodedAjaxError

type WebData
  = RemoteData AjaxError

type DecodedWebData
  = RemoteData DecodedAjaxError

type DecodedAjaxError
  = Either AjaxError MultipleErrors
