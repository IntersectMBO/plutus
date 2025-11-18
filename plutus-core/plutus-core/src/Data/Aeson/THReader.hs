{-# LANGUAGE TemplateHaskell #-}

module Data.Aeson.THReader where

import Data.Aeson
import Language.Haskell.TH.Syntax
import TH.RelativePaths

readJSONFromFile :: (FromJSON a, Lift a) => String -> Code Q a
readJSONFromFile name = liftCode $ do
  contents <- qReadFileLBS name
  case eitherDecode contents of
    Left err -> fail err
    Right res -> examineCode [||res||]
