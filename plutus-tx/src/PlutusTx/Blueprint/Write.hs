{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Blueprint.Write (
  encodeBlueprint,
  writeBlueprint,
) where

import Data.Aeson (toJSON)
import Data.Aeson.Encode.Pretty (encodePretty')
import Data.Aeson.Encode.Pretty qualified as Pretty
import Data.ByteString.Lazy qualified as LBS
import PlutusTx.Blueprint.Contract (Blueprint (..), ContractBlueprint)
import Prelude

writeBlueprint :: FilePath -> Blueprint -> IO ()
writeBlueprint f (MkBlueprint blueprint) = LBS.writeFile f (encodeBlueprint blueprint)

encodeBlueprint :: ContractBlueprint types -> LBS.ByteString
encodeBlueprint =
  encodePretty'
    Pretty.defConfig
      { Pretty.confIndent = Pretty.Spaces 2
      , Pretty.confCompare =
          Pretty.keyOrder
            [ "$id"
            , "$schema"
            , "$vocabulary"
            , "preamble"
            , "validators"
            , "definitions"
            , "title"
            , "description"
            , "version"
            , "plutusVersion"
            , "license"
            , "redeemer"
            , "datum"
            , "parameters"
            , "purpose"
            , "schema"
            ]
      , Pretty.confNumFormat = Pretty.Generic
      , Pretty.confTrailingNewline = True
      }
    . toJSON
