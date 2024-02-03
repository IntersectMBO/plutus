module Cardano.Constitution.DataFilePaths
    ( defaultConstitutionConfigFile
    ) where

import System.FilePath

defaultConstitutionConfigFile :: FilePath
defaultConstitutionConfigFile = "data" </> "defaultConstitution" <.> "json"
