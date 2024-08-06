{-# LANGUAGE TemplateHaskell #-}
module Data.Aeson.THReader where

import Data.Aeson
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Syntax.Compat
import TH.RelativePaths

readJSONFromFile :: (FromJSON a, Lift a) => String -> SpliceQ a
readJSONFromFile name = liftSplice $ do
    -- TODO: remove th-compat when we drop support for GHC 8.10
    contents <- qReadFileLBS name
    case eitherDecode contents of
        Left err  -> fail err
        Right res -> examineSplice [||res||]
