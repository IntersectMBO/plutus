{-# LANGUAGE TemplateHaskell #-}

module Data.Aeson.THReader where

import Data.Aeson
import System.IO.Unsafe

{-# OPAQUE readJSONFromFile #-}
readJSONFromFile :: FromJSON a => String -> a
readJSONFromFile path =
  case unsafePerformIO (eitherDecodeFileStrict path) of
    Left err -> error ("Failed to decode json file " <> path <> ":\n" <> err)
    Right res -> res
