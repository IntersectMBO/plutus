module Cardano.Constitution.DataFilePaths
    ( configJSONSchemaFile
    ) where

import System.FilePath

configJSONSchemaFile :: FilePath
configJSONSchemaFile =  "data" </> "config" <.> "schema.json"
