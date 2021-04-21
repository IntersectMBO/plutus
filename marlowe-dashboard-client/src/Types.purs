module Types
  ( AjaxResponse
  , DecodedAjaxResponse
  , WebData
  , DecodedWebData
  ) where

import Data.Either (Either)
import Data.List.NonEmpty (NonEmptyList)
import Foreign (ForeignError)
import Network.RemoteData (RemoteData)
import Servant.PureScript.Ajax (AjaxError)

type AjaxResponse
  = Either AjaxError

type DecodedAjaxResponse
  = Either (Either AjaxError (NonEmptyList ForeignError))

type WebData
  = RemoteData AjaxError

type DecodedWebData
  = RemoteData (Either AjaxError (NonEmptyList ForeignError))
