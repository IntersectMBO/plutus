{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Blueprint.Write
  ( encodeBlueprint
  , writeBlueprint
  ) where

import Data.Aeson (toJSON)
import Data.Aeson.Encode.Pretty (encodePretty')
import Data.Aeson.Encode.Pretty qualified as Pretty
import Data.ByteString.Lazy qualified as LBS
import PlutusTx.Blueprint.Contract (ContractBlueprint)
import Prelude

writeBlueprint :: FilePath -> ContractBlueprint -> IO ()
writeBlueprint f blueprint = LBS.writeFile f (encodeBlueprint blueprint)

encodeBlueprint :: ContractBlueprint -> LBS.ByteString
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
