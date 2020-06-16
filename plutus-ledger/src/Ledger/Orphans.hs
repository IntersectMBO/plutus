{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Ledger.Orphans where

import           Codec.Serialise.Class      (Serialise, decode, encode)
import           Crypto.Hash                (Digest, SHA256, digestFromByteString)
import           Data.Aeson                 (FromJSON (parseJSON), ToJSON (toJSON))
import qualified Data.Aeson                 as JSON
import qualified Data.Aeson.Extras          as JSON
import qualified Data.ByteArray             as BA
import qualified Data.ByteString            as BSS
import qualified Data.ByteString.Lazy       as BSL
import           IOTS                       (IotsType (iotsDefinition))
import           Language.PlutusTx          (Data)
import qualified Language.PlutusTx.AssocMap as Map
import qualified Language.PlutusTx.Prelude  as P
import           Type.Reflection            (Typeable)


{- [Note [Serialising Digests from Crypto.Hash]
This is more complicated than you might expect.  If you say
`encode = encode . BA.unpack` then the contents of the digest are
unpacked into a `Word8` list with 32 entries.  However, when cborg
serialises a list, every element in the output is preceded by a type
tag (in this case, 24), and this means that the serialised version is
about 64 bytes long, twice the length of the original data.  Packing
the `Word8` list into a `ByteString` first fixes this because cborg
just serialises it as a sequence of contiguous bytes. -}

instance Serialise (Digest SHA256) where
    encode = encode . BSS.pack . BA.unpack
    decode = do
      d :: BSS.ByteString <- decode
      let bs :: BA.Bytes = BA.pack . BSS.unpack $ d
      case digestFromByteString bs of
        Nothing -> fail $ "Couldn't decode SHA256 Digest: " ++ show d
        Just v  -> pure v

instance ToJSON (Digest SHA256) where
    toJSON = JSON.String . JSON.encodeSerialise

instance FromJSON (Digest SHA256) where
    parseJSON = JSON.decodeSerialise

instance IotsType (Digest SHA256) where
  iotsDefinition = iotsDefinition @String

instance IotsType P.ByteString where
  iotsDefinition = iotsDefinition @String

instance IotsType Data where
  iotsDefinition = iotsDefinition @String

instance (Typeable k, Typeable v, IotsType k, IotsType v) =>
         IotsType (Map.Map k v)

instance ToJSON BSL.ByteString where
    toJSON = JSON.String . JSON.encodeByteString . BSL.toStrict

instance FromJSON BSL.ByteString where
    parseJSON v = BSL.fromStrict <$> JSON.decodeByteString v
