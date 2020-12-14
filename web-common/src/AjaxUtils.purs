module AjaxUtils
  ( AjaxErrorPaneAction(..)
  , ajaxErrorPane
  , ajaxErrorRefLabel
  , renderForeignErrors
  , defaultJsonOptions
  ) where

import Prelude hiding (div)
import Bootstrap (alertDanger_, btn, floatRight)
import Data.Foldable (intercalate)
import Data.Maybe (Maybe(Just))
import Foreign (MultipleErrors, renderForeignError)
import Foreign.Generic.Class (Options, aesonSumEncoding, defaultOptions)
import Halogen (RefLabel(RefLabel))
import Halogen.HTML (ClassName(..), HTML, br_, button, div, div_, text)
import Halogen.HTML.Properties (class_, classes, ref)
import Halogen.HTML.Events (onClick)
import Icons (Icon(..), icon)
import Servant.PureScript.Ajax (AjaxError, ErrorDescription(..), runAjaxError)

data AjaxErrorPaneAction
  = CloseErrorPane

ajaxErrorPane :: forall p i. AjaxError -> HTML p i
ajaxErrorPane error =
  div
    [ class_ ajaxErrorClass
    , ref ajaxErrorRefLabel
    ]
    [ alertDanger_
        [ showAjaxError error
        , br_
        , helpText
        ]
    ]

closeableAjaxErrorPane :: forall p. AjaxError -> HTML p AjaxErrorPaneAction
closeableAjaxErrorPane error =
  div
    [ class_ ajaxErrorClass ]
    [ alertDanger_
        [ button
            [ classes [ btn, floatRight, ClassName "ajax-error-close-button" ]
            , onClick $ const $ Just CloseErrorPane
            ]
            [ icon Close ]
        , showAjaxError error
        , br_
        , helpText
        ]
    ]

ajaxErrorClass :: ClassName
ajaxErrorClass = ClassName "ajax-error"

helpText :: forall p i. HTML p i
helpText = text "Please try again or contact support for assistance."

ajaxErrorRefLabel :: RefLabel
ajaxErrorRefLabel = RefLabel "ajax-error"

showAjaxError :: forall p i. AjaxError -> HTML p i
showAjaxError = runAjaxError >>> _.description >>> showErrorDescription

showErrorDescription :: forall p i. ErrorDescription -> HTML p i
showErrorDescription (DecodingError err@"(\"Unexpected token E in JSON at position 0\" : Nil)") =
  div_
    [ text $ "Cannot connect to the server. Please check your network connection."
    , br_
    , text $ "DecodingError: " <> err
    ]

showErrorDescription (DecodingError err) = text $ "DecodingError: " <> err

showErrorDescription (ResponseFormatError err) = text $ "ResponseFormatError: " <> err

showErrorDescription (ConnectionError err) = text $ "ConnectionError: " <> err

renderForeignErrors :: MultipleErrors -> String
renderForeignErrors = intercalate "\n" <<< map renderForeignError

defaultJsonOptions :: Options
defaultJsonOptions =
  defaultOptions
    { unwrapSingleConstructors = true
    , sumEncoding = aesonSumEncoding
    }
