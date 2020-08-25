module View.Utils
  ( webDataPane
  , webDataPane2
  , webStreamDataPane
  , streamErrorPane
  ) where

import Prelude hiding (div)
import AjaxUtils (ajaxErrorPane)
import Bootstrap (alertDanger_)
import Data.Array as Array
import Data.Tuple.Nested (tuple2, uncurry2)
import Foreign (renderForeignError)
import Halogen.HTML (ClassName(..), HTML, br_, div, div_, text)
import Halogen.HTML.Properties (class_)
import Icons (Icon(..), icon)
import Network.RemoteData as Remote
import Network.StreamData as Stream
import Types (StreamError(..), WebData, WebStreamData)

-- | Make it easy to display successful `WebData` and render the other states in a consistent way.
webDataPane :: forall a p i. (a -> HTML p i) -> WebData a -> Array (HTML p i)
webDataPane successView (Remote.Success value) = [ successView value ]

webDataPane _ (Remote.Failure error) = [ ajaxErrorPane error ]

webDataPane _ (Remote.Loading) =
  [ div
      [ class_ $ ClassName "web-data-loading" ]
      [ icon Spinner ]
  ]

webDataPane successView (Remote.NotAsked) = webDataPane successView Remote.Loading

-- | `webDataPane` with two `WebData` arguments.
webDataPane2 :: forall a b p i. (a -> b -> HTML p i) -> WebData a -> WebData b -> Array (HTML p i)
webDataPane2 successView a b =
  webDataPane
    (uncurry2 successView)
    (tuple2 <$> a <*> b)

------------------------------------------------------------
streamDataRefreshing :: ClassName
streamDataRefreshing = ClassName "stream-data-refreshing"

streamDataRefreshingContent :: ClassName
streamDataRefreshingContent = streamDataRefreshing <> ClassName "-content"

-- | Make it easy to display successful `WebStreamData` and render the other states in a consistent way.
webStreamDataPane :: forall a p i. (a -> HTML p i) -> WebStreamData a -> Array (HTML p i)
webStreamDataPane successView (Stream.Success value) = [ successView value ]

webStreamDataPane successView (Stream.Refreshing value) =
  [ div
      [ class_ streamDataRefreshing ]
      [ icon Spinner
      , div [ class_ streamDataRefreshingContent ]
          [ successView value ]
      ]
  ]

webStreamDataPane _ (Stream.Failure error) = [ streamErrorPane error ]

webStreamDataPane _ (Stream.Loading) = [ icon Spinner ]

webStreamDataPane _ (Stream.NotAsked) = [ icon Spinner ]

streamErrorPane :: forall p i. StreamError -> HTML p i
streamErrorPane (TransportError error) = ajaxErrorPane error

streamErrorPane (ServerError error) =
  div
    [ class_ $ ClassName "ajax-error" ]
    [ alertDanger_
        [ div_ [ text error ]
        , br_
        , text "Please try again or contact support for assistance."
        ]
    ]

streamErrorPane (DecodingError errors) =
  div
    [ class_ $ ClassName "ajax-error" ]
    [ alertDanger_
        [ div_ (text <<< renderForeignError <$> Array.fromFoldable errors)
        , br_
        , text "Please try again or contact support for assistance."
        ]
    ]
