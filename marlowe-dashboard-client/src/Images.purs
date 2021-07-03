module Images
  ( marloweRunLogo
  , marloweRunNavLogo
  , marloweRunNavLogoDark
  , backgroundShape
  , arrowBack
  , linkHighlight
  , getStartedThumbnail
  ) where

foreign import marloweRunLogo_ :: String

foreign import marloweRunNavLogo_ :: String

foreign import marloweRunNavLogoDark_ :: String

foreign import backgroundShape_ :: String

foreign import arrowBack_ :: String

foreign import linkHighlight_ :: String

foreign import getStartedThumbnail_ :: String

marloweRunLogo :: String
marloweRunLogo = marloweRunLogo_

marloweRunNavLogo :: String
marloweRunNavLogo = marloweRunNavLogo_

marloweRunNavLogoDark :: String
marloweRunNavLogoDark = marloweRunNavLogoDark_

backgroundShape :: String
backgroundShape = backgroundShape_

arrowBack :: String
arrowBack = arrowBack_

linkHighlight :: String
linkHighlight = linkHighlight_

getStartedThumbnail :: String
getStartedThumbnail = getStartedThumbnail_
