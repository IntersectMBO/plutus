module View.Utils (webDataPane) where

import Halogen.HTML (HTML)
import AjaxUtils (ajaxErrorPane)
import Icons (Icon(..), icon)
import Network.RemoteData (RemoteData(..))
import Types (WebData)

webDataPane :: forall a p i. (a -> HTML p i) -> WebData a -> Array (HTML p i)
webDataPane successView (Success report) = [ successView report ]

webDataPane _ (Failure error) = [ ajaxErrorPane error ]

webDataPane _ (Loading) = [ icon Spinner ]

webDataPane _ (NotAsked) = [ icon Spinner ]
