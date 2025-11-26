module Cardano.Constitution.DataFilePaths
  ( defaultConstitutionConfigFile
  , defaultConstitutionJSONSchemaFile
  ) where

import System.FilePath

defaultConstitutionConfigFile :: FilePath
defaultConstitutionConfigFile = "data" </> "defaultConstitution" <.> "json"

defaultConstitutionJSONSchemaFile :: FilePath
defaultConstitutionJSONSchemaFile = defaultConstitutionConfigFile `replaceExtension` "schema.json"
