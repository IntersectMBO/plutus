{-# LANGUAGE TemplateHaskell #-}

module Data.Aeson.THReader where

import Data.Aeson
import Language.Haskell.TH.Syntax
import System.IO.Unsafe
import TH.RelativePaths

{-# OPAQUE readJSONFromFile #-}
readJSONFromFile :: FromJSON a => String -> a
readJSONFromFile path =
  case unsafePerformIO (eitherDecodeFileStrict path) of
    Left err -> error ("Failed to decode json file " <> path <> ":\n" <> err)
    Right res -> res
