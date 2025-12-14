{-# LANGUAGE OverloadedStrings #-}

module PlutusLedgerApi.Envelope
  ( compiledCodeEnvelope
  , compiledCodeEnvelopeForVersion
  , writeCodeEnvelope
  , writeCodeEnvelopeForVersion
  ) where

import Data.Aeson ((.=))
import Data.Aeson qualified as Json
import Data.Aeson.Encode.Pretty qualified as Json
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Short qualified as BS
import Data.Text (Text)
import Data.Text.Encoding (decodeUtf8)
import PlutusLedgerApi.Common.SerialisedScript (serialiseCompiledCode)
import PlutusLedgerApi.Common.Versions (PlutusLedgerLanguage (..))
import PlutusTx.Code (CompiledCode)

{-| Produce a JSON envelope containing 'CompiledCode' serialised with
CBOR and encoded in Base 16 (aka. HEX), using PlutusV3 by default.

"Envelope" is a JSON object with the following fields:
@
{
  "type": "PlutusScriptV3",
  "description": "A description of the code",
  "cborHex": "..."
}
@ -}
compiledCodeEnvelope
  :: Text
  -- ^ Description of the code
  -> CompiledCode a
  -- ^ Compiled code to wrap in the envelope
  -> Json.Value
  -- ^ JSON envelope
compiledCodeEnvelope = compiledCodeEnvelopeForVersion PlutusV3

{-| Produce a JSON envelope containing 'CompiledCode' serialised with
CBOR and encoded in Base 16 (aka. HEX).

"Envelope" is a JSON object with the following fields:
@
{
  "type": "PlutusScriptV2",
  "description": "A description of the code",
  "cborHex": "..."
}
@ -}
compiledCodeEnvelopeForVersion
  :: PlutusLedgerLanguage
  -- ^ Language of the compiled code, e.g. 'PlutusLedgerLanguage.PlutusV3'
  -> Text
  -- ^ Description of the code
  -> CompiledCode a
  -- ^ Compiled code to wrap in the envelope
  -> Json.Value
  -- ^ JSON envelope
compiledCodeEnvelopeForVersion lang desc code =
  Json.object
    [ "type" .= typ
    , "description" .= desc
    , "cborHex" .= hex
    ]
  where
    typ :: Text =
      case lang of
        PlutusV1 -> "PlutusScriptV1"
        PlutusV2 -> "PlutusScriptV2"
        PlutusV3 -> "PlutusScriptV3"

    hex = decodeUtf8 (Base16.encode (BS.fromShort (serialiseCompiledCode code)))

{-|
Write a JSON envelope containing 'CompiledCode' serialised with
CBOR and encoded in Base 16 (aka. HEX) to a file on disk, using PlutusV3 by default.

"Envelope" is a JSON object with the following fields:
@
{
  "type": "PlutusScriptV3",
  "description": "A description of the code",
  "cborHex": "..."
}
@ -}
writeCodeEnvelope
  :: Text
  -- ^ Description of the code
  -> CompiledCode a
  -- ^ Compiled code to wrap in the envelope
  -> FilePath
  -- ^ File path to write the envelope to
  -> IO ()
writeCodeEnvelope = writeCodeEnvelopeForVersion PlutusV3

{-|
Write a JSON envelope containing 'CompiledCode' serialised with
CBOR and encoded in Base 16 (aka. HEX) to a file on disk.

"Envelope" is a JSON object with the following fields:
@
{
  "type": "PlutusScriptV2",
  "description": "A description of the code",
  "cborHex": "..."
}
@ -}
writeCodeEnvelopeForVersion
  :: PlutusLedgerLanguage
  -- ^ Language of the compiled code, e.g. 'PlutusLedgerLanguage.PlutusV3'
  -> Text
  -- ^ Description of the code
  -> CompiledCode a
  -- ^ Compiled code to wrap in the envelope
  -> FilePath
  -- ^ File path to write the envelope to
  -> IO ()
writeCodeEnvelopeForVersion lang desc code path = do
  let envelope = compiledCodeEnvelopeForVersion lang desc code
      -- aeson-pretty doesn't add a newline at the end, so we add it manually
      envelopePretty = Json.encodePretty' config envelope <> "\n"
  LBS.writeFile path envelopePretty
  where
    config =
      Json.defConfig
        { Json.confCompare =
            Json.keyOrder ["type", "description", "cborHex"]
        }
