module AjaxUtils where

import Prelude (show, (<>), (>>>))
import Servant.PureScript.Affjax (AjaxError, ErrorDescription(ConnectionError, DecodingError, ParsingError, UnexpectedHTTPStatus), runAjaxError)

showAjaxError :: AjaxError -> String
showAjaxError =
  runAjaxError >>> _.description >>> showErrorDescription

showErrorDescription :: ErrorDescription -> String
showErrorDescription (UnexpectedHTTPStatus {status, response}) = response <> " " <> show status
showErrorDescription (ParsingError err) = err
showErrorDescription (DecodingError err) = err
showErrorDescription (ConnectionError err) = err
