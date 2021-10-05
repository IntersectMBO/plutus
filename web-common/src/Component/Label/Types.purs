module Component.Label.Types
  ( Input
  , Variant(..)
  ) where

data Variant
  = Above
  | Nested

type Input
  = { for :: String
    , text :: String
    , variant :: Variant
    }
