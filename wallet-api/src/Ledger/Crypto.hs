{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
module Ledger.Crypto(
    PubKey(..)
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

import           Codec.Serialise.Class      (Serialise)
import           Control.Newtype.Generics   (Newtype)
import qualified Crypto.ECC.Ed25519Donna    as ED25519
import           Crypto.Error               (throwCryptoError)
import           Data.Aeson                 (FromJSON (parseJSON), FromJSONKey, ToJSON (toJSON), ToJSONKey)
import qualified Data.Aeson                 as JSON
import qualified Data.Aeson.Extras          as JSON
import qualified Data.ByteArray             as BA
import qualified Data.ByteString            as BS
import qualified Data.ByteString.Lazy       as BSL
import           Data.Swagger               (ToSchema (declareNamedSchema), byteSchema)
import           Data.Swagger.Internal
import           GHC.Generics               (Generic)
import           KeyBytes                   (KeyBytes)
import qualified KeyBytes                   as KB
import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Lift     (makeLift)
import           Ledger.TxId
import           Servant.API                (FromHttpApiData (parseUrlPiece), ToHttpApiData (toUrlPiece))

-- | A cryptographic public key.
newtype PubKey = PubKey { getPubKey :: KeyBytes }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON, Newtype, ToJSONKey, FromJSONKey)
    deriving newtype (Serialise)
makeLift ''PubKey

-- | A cryptographic private key.
newtype PrivateKey = PrivateKey { getPrivateKey :: KeyBytes }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON, Newtype, ToJSONKey, FromJSONKey)
    deriving newtype (Serialise)

makeLift ''PrivateKey

instance ToHttpApiData PrivateKey where
    toUrlPiece = toUrlPiece . getPrivateKey

instance FromHttpApiData PrivateKey where
    parseUrlPiece a = PrivateKey <$> parseUrlPiece a

-- | A message with a cryptographic signature.
newtype Signature = Signature { getSignature :: Builtins.SizedByteString 64 }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)
    deriving newtype (Serialise)

instance ToSchema Signature where
    declareNamedSchema _ = pure $ NamedSchema (Just "Signature") byteSchema

instance ToJSON Signature where
    toJSON = JSON.String . JSON.encodeByteString . BSL.toStrict . Builtins.unSizedByteString . getSignature

instance FromJSON Signature where
    parseJSON v = Signature . Builtins.SizedByteString . BSL.fromStrict <$> JSON.decodeByteString v

makeLift ''Signature

-- | Check whether the given 'Signature' was signed by the private key corresponding to the given public key.
signedBy :: Signature -> PubKey -> TxId -> Bool
signedBy (Signature s) (PubKey k) txId =
    let k' = ED25519.publicKey $ BSL.toStrict $ Builtins.unSizedByteString $ KB.getKeyBytes k
        s' = ED25519.signature $ BSL.toStrict $ Builtins.unSizedByteString s
    in throwCryptoError $ ED25519.verify <$> k' <*> pure (getTxId txId) <*> s' -- TODO: is this what we want

-- | Sign the hash of a transaction using a private key.
signTx :: TxId -> PrivateKey -> Signature
signTx (TxIdOf txId) = sign txId

-- | Sign a message using a private key.
sign :: BA.ByteArrayAccess a => a -> PrivateKey -> Signature
sign  msg (PrivateKey privKey) =
    let k  = ED25519.secretKey $ BSL.toStrict $ Builtins.unSizedByteString $ KB.getKeyBytes privKey
        pk = ED25519.toPublic <$> k
        salt :: BS.ByteString
        salt = "" -- TODO: do we need better salt?
        convert = Signature . Builtins.SizedByteString . BSL.pack . BA.unpack
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
