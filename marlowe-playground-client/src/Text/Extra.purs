module Text.Extra where

import Prelude
import Data.Maybe (fromMaybe)
import Data.String (Pattern(..), stripPrefix, stripSuffix, take, trim)

stripParens :: String -> String
stripParens s =
  if take 1 s == "(" then
    fromMaybe s
      $ do
          withoutPrefix <- stripPrefix (Pattern "(") $ trim s
          withoutSuffix <- stripSuffix (Pattern ")") withoutPrefix
          pure withoutSuffix
  else
    s
