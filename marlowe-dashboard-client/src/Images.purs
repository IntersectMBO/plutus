module Images
  ( marloweRunLogo
  , marloweRunNavLogo
  , marloweRunNavLogoDark
  , arrowBack
  , linkHighlight
  ) where

foreign import marloweRunLogo_ :: String

foreign import marloweRunNavLogo_ :: String

foreign import marloweRunNavLogoDark_ :: String

foreign import arrowBack_ :: String

foreign import linkHighlight_ :: String

marloweRunLogo :: String
marloweRunLogo = marloweRunLogo_

marloweRunNavLogo :: String
marloweRunNavLogo = marloweRunNavLogo_

marloweRunNavLogoDark :: String
marloweRunNavLogoDark = marloweRunNavLogoDark_

arrowBack :: String
arrowBack = arrowBack_

linkHighlight :: String
linkHighlight = linkHighlight_
