module Data.String.Extra
       (abbreviate
       ) where

import Data.String as String
import Prelude ((<=), (<>))

abbreviate :: String -> String
abbreviate str =
  if String.length str <= 7
  then str
  else String.take 7 str <> "..."
