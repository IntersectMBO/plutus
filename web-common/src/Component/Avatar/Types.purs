module Component.Avatar.Types (Input, Size(..)) where

data Size
  = Small
  | Medium
  | Large

type Input
  = { nickname :: String
    , size :: Size
    , background :: Array String
    }
