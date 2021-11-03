-- | Encoding and decoding of 'ByteString' and serialisable values
--   as base16 encoded JSON strings
module Data.Aeson.Extras(
      encodeByteString
    , decodeByteString
    , encodeSerialise
    , decodeSerialise
    , tryDecode
    , JSONViaSerialise (..)
    ) where

import Codec.CBOR.Write qualified as Write
import Codec.Serialise (Serialise, deserialiseOrFail, encode)
import Control.Monad ((>=>))
import Data.Aeson qualified as Aeson
import Data.Aeson.Types qualified as Aeson
import Data.Bifunctor (first)
import Data.ByteString qualified as BSS
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Lazy qualified as BSL
import Data.Text qualified as Text
import Data.Text.Encoding qualified as TE

encodeByteString :: BSS.ByteString -> Text.Text
encodeByteString = TE.decodeUtf8 . Base16.encode

tryDecode :: Text.Text -> Either String BSS.ByteString
tryDecode = Base16.decode . TE.encodeUtf8

decodeByteString :: Aeson.Value -> Aeson.Parser BSS.ByteString
decodeByteString = Aeson.withText "ByteString" (either fail pure . tryDecode)

encodeSerialise :: Serialise a => a -> Text.Text
encodeSerialise = encodeByteString . Write.toStrictByteString . encode

decodeSerialise :: Serialise a => Aeson.Value -> Aeson.Parser a
decodeSerialise = decodeByteString >=> go where
    go bs =
        case first show $ deserialiseOrFail $ BSL.fromStrict bs of
            Left e  -> fail e
            Right v -> pure v

-- | Newtype for deriving 'ToJSON' and 'FromJSON' for types that have a 'Serialise'
-- instance by just encoding the serialized bytes as a JSON string.
newtype JSONViaSerialise a = JSONViaSerialise a

instance Serialise a => Aeson.ToJSON (JSONViaSerialise a) where
    toJSON (JSONViaSerialise a) = Aeson.String $ encodeSerialise a

instance Serialise a => Aeson.FromJSON (JSONViaSerialise a) where
    parseJSON v = JSONViaSerialise <$> decodeSerialise v
