{-# LANGUAGE TemplateHaskell #-}
module Data.Aeson.THReader where

import Data.Aeson
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import qualified Data.ByteString.Lazy as BSL

readJSONFromFile :: (FromJSON a, Lift a) => String -> Q (TExp a)
readJSONFromFile name = do
    addDependentFile name
    contents <- runIO $ BSL.readFile name
    case (eitherDecode contents) of
        Left err -> error err
        Right res -> [||res||]