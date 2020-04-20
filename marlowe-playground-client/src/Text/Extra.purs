module Text.Extra where

import Prelude
import Data.Maybe (fromMaybe)
import Data.String (Pattern(..), stripPrefix, stripSuffix, trim)

stripParens :: String -> String
stripParens s =
  fromMaybe s
    $ do
        withoutPrefix <- stripPrefix (Pattern "(") $ trim s
        withoutSuffix <- stripSuffix (Pattern ")") withoutPrefix
        pure withoutSuffix
