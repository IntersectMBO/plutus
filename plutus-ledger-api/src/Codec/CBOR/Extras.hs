module Codec.CBOR.Extras where

import Codec.CBOR.Decoding as CBOR
import Codec.Serialise (Serialise, decode, encode)
import Flat qualified
import Flat.Decoder qualified as Flat

-- | Newtype to provide 'Serialise' instances for types with a 'Flat' instance that
-- just encodes the flat-serialized value as a CBOR bytestring
newtype SerialiseViaFlat a = SerialiseViaFlat a
instance Flat.Flat a => Serialise (SerialiseViaFlat a) where
  encode (SerialiseViaFlat a) = encode $ Flat.flat a
  decode = SerialiseViaFlat <$> (decodeViaFlat (Flat.decode))

decodeViaFlat :: Flat.Get a -> CBOR.Decoder s a
decodeViaFlat decoder = do
    bs <- decodeBytes
    case Flat.unflatWith decoder bs of
        Left  err -> fail (show err)
        Right v   -> pure v
