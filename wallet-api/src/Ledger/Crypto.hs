{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
module Ledger.Crypto where

import           Codec.Serialise.Class      (Serialise)
import           Control.Newtype.Generics   (Newtype)
import qualified Crypto.ECC.Ed25519Donna    as ED25519
import           Crypto.Error               (throwCryptoError)
import           Data.Aeson                 (FromJSON (parseJSON), FromJSONKey, ToJSON (toJSON), ToJSONKey)
import qualified Data.ByteArray             as BA
import qualified Data.ByteString            as BS
import qualified Data.ByteString.Lazy       as BSL
import           Data.Swagger               (ToSchema (declareNamedSchema))
import           GHC.Generics               (Generic)
import           KeyBytes                   (KeyBytes)
import qualified KeyBytes                   as KB
import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Lift     (makeLift)
import           Ledger.TxId
import           Servant.API                (FromHttpApiData (parseUrlPiece), ToHttpApiData(toUrlPiece))

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
    toUrlPiece = undefined

instance FromHttpApiData PrivateKey where
    parseUrlPiece = undefined

-- | A message with a cryptographic signature.
-- NOTE: relies on incorrect notion of signatures
newtype Signature = Signature { getSignature :: Builtins.SizedByteString 64 }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)
    -- deriving anyclass (ToSchema, ToJSON, FromJSON)
    deriving newtype (Serialise)

instance ToSchema Signature where
    declareNamedSchema _ = undefined

instance ToJSON Signature where
    toJSON = undefined

instance FromJSON Signature where
    parseJSON = undefined

makeLift ''Signature

-- | Check whether the given 'Signature' was signed by the private key corresponding to the given public key.
signedBy :: Signature -> PubKey -> TxId -> Bool
signedBy (Signature s) (PubKey k) txId =
    let k' = ED25519.publicKey $ BSL.toStrict $ Builtins.unSizedByteString $ KB.getKeyBytes k
        s' = ED25519.signature $ BSL.toStrict $ Builtins.unSizedByteString s
    in throwCryptoError $ ED25519.verify <$> k' <*> pure (getTxId txId) <*> s' -- TODO: is this what we want

-- | Sign the hash of a transaction using a private key.
sign :: TxId -> PrivateKey -> Signature
sign (TxIdOf txId) (PrivateKey privKey) =
    let k  = ED25519.secretKey $ BSL.toStrict $ Builtins.unSizedByteString $ KB.getKeyBytes privKey
        pk = ED25519.toPublic <$> k
        salt :: BS.ByteString
        salt = "" -- TODO: do we need better salt?
        convert = Signature . Builtins.SizedByteString . BSL.pack . BA.unpack
    in throwCryptoError $ fmap convert (ED25519.sign <$> k <*> pure salt <*> pk <*> pure txId)

fromHex :: BSL.ByteString -> PrivateKey
fromHex = PrivateKey . KB.fromHex

-- TODO: Instance ByteArrayAccess PrivateKey
-- TODO: Instance ByteArrayAccess PubKey

toPublicKey :: PrivateKey -> PubKey
toPublicKey = PubKey . KB.fromBytes . BSL.pack . BA.unpack . ED25519.toPublic . f . KB.bytes . getPrivateKey where
    f = throwCryptoError . ED25519.secretKey . BSL.toStrict
