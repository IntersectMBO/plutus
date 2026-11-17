{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Assurance.Write
  ( encodeAssurance
  , writeAssurance
  , blueprintRef
  ) where

import Prelude

import Data.Aeson (toJSON)
import Data.Aeson.Encode.Pretty (encodePretty')
import Data.Aeson.Encode.Pretty qualified as Pretty
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Lazy qualified as LBS
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import PlutusCore.Crypto.Hash (sha2_256)
import PlutusTx.Assurance.Document (AssuranceDocument, BlueprintRef (..), Digest (..))

writeAssurance :: FilePath -> AssuranceDocument -> IO ()
writeAssurance f = LBS.writeFile f . encodeAssurance

encodeAssurance :: AssuranceDocument -> LBS.ByteString
encodeAssurance =
  encodePretty'
    Pretty.defConfig
      { Pretty.confIndent = Pretty.Spaces 2
      , Pretty.confCompare =
          Pretty.keyOrder
            [ "$schema"
            , "preamble"
            , "blueprint"
            , "languages"
            , "tools"
            , "formalFragments"
            , "properties"
            , "id"
            , "title"
            , "name"
            , "description"
            , "version"
            , "authors"
            , "created"
            , "license"
            , "uri"
            , "hash"
            , "alg"
            , "digest"
            , "language"
            , "imports"
            , "uses"
            , "source"
            , "scope"
            , "validators"
            , "statement"
            , "text"
            , "formal"
            ]
      , Pretty.confNumFormat = Pretty.Generic
      , Pretty.confTrailingNewline = True
      }
    . toJSON

{-| Build the blueprint reference for an already-written @plutus.json@, hashing
the bytes on disk.

Order matters: the CIP requires the digest to be over the blueprint document
exactly as retrieved, so this must run *after* 'PlutusTx.Blueprint.writeBlueprint'
and before 'writeAssurance'. -}
blueprintRef :: Text -> FilePath -> IO BlueprintRef
blueprintRef uri path = do
  bytes <- BS.readFile path
  pure
    MkBlueprintRef
      { blueprintUri = uri
      , blueprintHash =
          Just (MkDigest "sha256" (Text.decodeUtf8 (Base16.encode (sha2_256 bytes))))
      }
