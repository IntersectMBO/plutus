module AjaxUtils where

import Bootstrap (alertDanger_)
import Halogen.HTML (ClassName(..), HTML, br_, div, text)
import Halogen.HTML.Properties (class_)
import Playground.Server (SPParams_(..))
import Prelude (($), (<>), (>>>))
import Servant.PureScript.Ajax (AjaxError, ErrorDescription(..), runAjaxError)
import Servant.PureScript.Settings (SPSettings_, defaultSettings)

ajaxSettings :: SPSettings_ SPParams_
ajaxSettings =
  defaultSettings $ SPParams_ { baseURL: "/api/" }

showAjaxError :: forall p i. AjaxError -> HTML p i
showAjaxError =
  runAjaxError >>> _.description >>> showErrorDescription

showErrorDescription :: forall p i. ErrorDescription -> HTML p i
showErrorDescription (DecodingError err) = text $ "DecodingError: " <> err
showErrorDescription (ResponseFormatError err) = text $ "ResponseFormatError: " <> err
showErrorDescription (ConnectionError err) = text $ "ConnectionError: " <> err

ajaxErrorPane :: forall p i. AjaxError -> HTML p i
ajaxErrorPane error =
  div
    [ class_ $ ClassName "ajax-error" ]
    [ alertDanger_
        [ showAjaxError error
        , br_
        , text "Please try again or contact support for assistance."
        ]
    ]
