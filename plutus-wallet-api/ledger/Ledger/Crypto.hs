{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.Crypto(
    PubKey(..)
    , PubKeyHash(..)
    , pubKeyHash
    , PrivateKey(..)
    , Signature(..)
    , signedBy
    , sign
    , signTx
    , fromHex
    , toPublicKey
    -- $privateKeys
    , knownPrivateKeys
    , privateKey1
    , privateKey2
    , privateKey3
    , privateKey4
    , privateKey5
    , privateKey6
    , privateKey7
    , privateKey8
    , privateKey9
    , privateKey10
    ) where

import qualified Codec.CBOR.Write           as Write
import           Codec.Serialise.Class      (Serialise)
import           Codec.Serialise.Class      (encode)
import           Control.Newtype.Generics   (Newtype)
import qualified Crypto.ECC.Ed25519Donna    as ED25519
import           Crypto.Error               (throwCryptoError)
import           Crypto.Hash                (Digest, SHA256, hash)
import           Data.Aeson                 (FromJSON (parseJSON), FromJSONKey, ToJSON (toJSON), ToJSONKey, (.:))
import qualified Data.Aeson                 as JSON
import qualified Data.Aeson.Extras          as JSON
import qualified Data.ByteArray             as BA
import qualified Data.ByteString            as BS
import qualified Data.ByteString.Lazy       as BSL
import           Data.Hashable              (Hashable)
import           Data.String
import           Data.Text.Prettyprint.Doc
import           GHC.Generics               (Generic)
import           IOTS                       (IotsType)
import qualified Language.PlutusTx          as PlutusTx
import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Lift     (makeLift)
import qualified Language.PlutusTx.Prelude  as P
import           Ledger.Orphans             ()
import           Ledger.TxId
import           LedgerBytes                (LedgerBytes)
import qualified LedgerBytes                as KB
import           Servant.API                (FromHttpApiData (parseUrlPiece), ToHttpApiData (toUrlPiece))

-- | A cryptographic public key.
newtype PubKey = PubKey { getPubKey :: LedgerBytes }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass ( ToJSON, FromJSON, Newtype, ToJSONKey, FromJSONKey, IotsType)
    deriving newtype (P.Eq, P.Ord, Serialise, PlutusTx.IsData)
    deriving IsString via LedgerBytes
    deriving Pretty via LedgerBytes
makeLift ''PubKey

-- | The hash of a public key. This is frequently used to identify the public key, rather than the key itself.
newtype PubKeyHash = PubKeyHash { getPubKeyHash :: BSL.ByteString }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass ( ToJSON, FromJSON, Newtype, ToJSONKey, FromJSONKey, IotsType)
    deriving newtype (P.Eq, P.Ord, Serialise, PlutusTx.IsData, Hashable)
    -- TODO: this should be here, but it upsets marlowe a bit. Should be fixed in the future.
    --deriving IsString via LedgerBytes
    deriving Pretty via LedgerBytes
makeLift ''PubKeyHash

-- | Compute the hash of a public key.
pubKeyHash :: PubKey -> PubKeyHash
pubKeyHash pk = PubKeyHash $ BSL.fromStrict $ BA.convert h' where
    h :: Digest SHA256 = hash $ Write.toStrictByteString e
    h' :: Digest SHA256 = hash h
    e = encode pk

-- | A cryptographic private key.
newtype PrivateKey = PrivateKey { getPrivateKey :: LedgerBytes }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass ( ToJSON, FromJSON, Newtype, ToJSONKey, FromJSONKey)
    deriving newtype (P.Eq, P.Ord, Serialise, PlutusTx.IsData)
    deriving Pretty via LedgerBytes

makeLift ''PrivateKey

instance ToHttpApiData PrivateKey where
    toUrlPiece = toUrlPiece . getPrivateKey

instance FromHttpApiData PrivateKey where
    parseUrlPiece a = PrivateKey <$> parseUrlPiece a

-- | A message with a cryptographic signature.
newtype Signature = Signature { getSignature :: Builtins.ByteString }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (IotsType)
    deriving newtype (P.Eq, P.Ord, Serialise, PlutusTx.IsData)
    deriving Pretty via LedgerBytes

instance ToJSON Signature where
  toJSON signature =
    JSON.object
      [ ( "getSignature"
        , JSON.String .
          JSON.encodeByteString .
          BSL.toStrict . getSignature $
          signature)
      ]

instance FromJSON Signature where
  parseJSON =
    JSON.withObject "Signature" $ \object -> do
      raw <- object .: "getSignature"
      bytes <- JSON.decodeByteString raw
      pure . Signature . BSL.fromStrict $ bytes

makeLift ''Signature

-- | Check whether the given 'Signature' was signed by the private key corresponding to the given public key.
signedBy :: Signature -> PubKey -> TxId -> Bool
signedBy (Signature s) (PubKey k) txId =
    let k' = ED25519.publicKey $ BSL.toStrict $ KB.getLedgerBytes k
        s' = ED25519.signature $ BSL.toStrict s
    in throwCryptoError $ ED25519.verify <$> k' <*> pure (BSL.toStrict $ getTxId txId) <*> s' -- TODO: is this what we want

-- | Sign the hash of a transaction using a private key.
signTx :: TxId -> PrivateKey -> Signature
signTx (TxId txId) = sign $ BSL.toStrict txId

-- | Sign a message using a private key.
sign :: BA.ByteArrayAccess a => a -> PrivateKey -> Signature
sign  msg (PrivateKey privKey) =
    let k  = ED25519.secretKey $ BSL.toStrict $ KB.getLedgerBytes privKey
        pk = ED25519.toPublic <$> k
        salt :: BS.ByteString
        salt = "" -- TODO: do we need better salt?
        convert = Signature . BSL.pack . BA.unpack
    in throwCryptoError $ fmap convert (ED25519.sign <$> k <*> pure salt <*> pk <*> pure msg)

fromHex :: BSL.ByteString -> PrivateKey
fromHex = PrivateKey . KB.fromHex

toPublicKey :: PrivateKey -> PubKey
toPublicKey = PubKey . KB.fromBytes . BSL.pack . BA.unpack . ED25519.toPublic . f . KB.bytes . getPrivateKey where
    f = throwCryptoError . ED25519.secretKey . BSL.toStrict

-- $privateKeys
-- 'privateKey1', 'privateKey2', ... 'privateKey10' are ten predefined 'PrivateKey' values.
--
-- The private keys can be found in the 'sign.input' file linked from
-- http://ed25519.cr.yp.to/software.html.

privateKey1, privateKey2, privateKey3, privateKey4, privateKey5, privateKey6, privateKey7, privateKey8, privateKey9, privateKey10 :: PrivateKey
privateKey1 = fromHex "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
privateKey2 = fromHex "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb"
privateKey3 = fromHex "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7"
privateKey4 = fromHex "691865bfc82a1e4b574eecde4c7519093faf0cf867380234e3664645c61c5f79"
privateKey5 = fromHex "3b26516fb3dc88eb181b9ed73f0bcd52bcd6b4c788e4bcaf46057fd078bee073"
privateKey6 = fromHex "edc6f5fbdd1cee4d101c063530a30490b221be68c036f5b07d0f953b745df192"
privateKey7 = fromHex "a980f892db13c99a3e8971e965b2ff3d41eafd54093bc9f34d1fd22d84115bb6"
privateKey8 = fromHex "9acad959d216212d789a119252ebfe0c96512a23c73bd9f3b202292d6916a738"
privateKey9 = fromHex "d5aeee41eeb0e9d1bf8337f939587ebe296161e6bf5209f591ec939e1440c300"
privateKey10 = fromHex "0a47d10452ae2febec518a1c7c362890c3fc1a49d34b03b6467d35c904a8362d"

-- | A list of 10 private keys.
--   TODO: Generate random private keys (I couldn't find a way to
--         do this in 'Crypto.ECC.Ed25519Donna' in 'cardano-crypto')
knownPrivateKeys :: [PrivateKey]
knownPrivateKeys = [privateKey1, privateKey2, privateKey3, privateKey4, privateKey5, privateKey6, privateKey7, privateKey8, privateKey9, privateKey10]
