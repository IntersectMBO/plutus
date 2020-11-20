-- | Encoding and decoding of 'ByteString' and serialisable values
--   as base16 encoded JSON strings
module Data.Aeson.Extras(
      encodeByteString
    , decodeByteString
    , encodeSerialise
    , decodeSerialise
    , tryDecode
    ) where

import qualified Codec.CBOR.Write       as Write
import           Codec.Serialise        (Serialise, deserialiseOrFail, encode)
import           Control.Monad          ((>=>))
import qualified Data.Aeson             as Aeson
import qualified Data.Aeson.Types       as Aeson
import           Data.Bifunctor         (first)
import qualified Data.ByteString        as BSS
import qualified Data.ByteString.Base16 as Base16
import qualified Data.ByteString.Lazy   as BSL
import qualified Data.Text              as Text
import qualified Data.Text.Encoding     as TE

encodeByteString :: BSS.ByteString -> Text.Text
encodeByteString = TE.decodeUtf8 . Base16.encode

tryDecode :: Text.Text -> Either String BSS.ByteString
tryDecode s =
    let (eun16, rest) = Base16.decode . TE.encodeUtf8 $ s in
    if BSS.null rest
    then Right eun16
    else Left "failed to decode base16"

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
            Right v -> pure v
