module Logo
  ( marloweRunLogo
  , marloweRunNavLogo
  , marloweRunNavLogoDark
  ) where

foreign import marloweRunLogo_ :: String

foreign import marloweRunNavLogo_ :: String

foreign import marloweRunNavLogoDark_ :: String

marloweRunLogo :: String
marloweRunLogo = marloweRunLogo_

marloweRunNavLogo :: String
marloweRunNavLogo = marloweRunNavLogo_

marloweRunNavLogoDark :: String
marloweRunNavLogoDark = marloweRunNavLogoDark_
