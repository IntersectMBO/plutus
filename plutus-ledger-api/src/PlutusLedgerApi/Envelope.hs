{-# LANGUAGE OverloadedStrings #-}

module PlutusLedgerApi.Envelope (compiledCodeEnvelope, writeCodeEnvelope) where

import Data.Aeson ((.=))
import Data.Aeson qualified as Json
import Data.Aeson.Encode.Pretty qualified as Json
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Short qualified as BS
import Data.Text (Text)
import Data.Text.Encoding (decodeUtf8)
import PlutusLedgerApi.Common.SerialisedScript (serialiseCompiledCode)
import PlutusTx.Code (CompiledCode)

{-| Produce a JSON envelope containing 'CompiledCode' serialised with
CBOR and encoded in Base 16 (aka. HEX).

"Envelope" is a JSON object with the following fields:
@
{
  "type": "PlutusScriptV3",
  "description": "A description of the code",
  "cborHex": "..."
}
@
-}
compiledCodeEnvelope
  :: Text
  -- ^ Description of the code
  -> CompiledCode a
  -- ^ Compiled code to wrap in the envelope
  -> Json.Value
  -- ^ JSON envelope
compiledCodeEnvelope desc code =
  Json.object ["type" .= typ, "description" .= desc, "cborHex" .= hex]
 where
  typ :: Text
  typ = "PlutusScriptV3"

  hex = decodeUtf8 (Base16.encode (BS.fromShort (serialiseCompiledCode code)))

{-| Write a JSON envelope containing 'CompiledCode' serialised with
CBOR and encoded in Base 16 (aka. HEX) to a file on disk.

"Envelope" is a JSON object with the following fields:
@
{
  "type": "PlutusScriptV3",
  "description": "A description of the code",
  "cborHex": "..."
}
@
-}
writeCodeEnvelope
  :: Text
  -- ^ Description of the code
  -> CompiledCode a
  -- ^ Compiled code to wrap in the envelope
  -> FilePath
  -- ^ File path to write the envelope to
  -> IO ()
writeCodeEnvelope desc code path = do
  let envelope = Json.encodePretty' config (compiledCodeEnvelope desc code)
  -- aeson-pretty doesn't add a newline at the end, so we add it manually
  LBS.writeFile path (envelope <> "\n")
 where
  config =
    Json.defConfig
      { Json.confCompare = Json.keyOrder ["type", "description", "cborHex"]
      }
