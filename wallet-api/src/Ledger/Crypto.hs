{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
module Ledger.Crypto where

import           Codec.Serialise.Class        (Serialise)
import           Control.Newtype.Generics     (Newtype)
import qualified Crypto.ECC.Ed25519Donna      as ED25519
import           Crypto.Error                 (throwCryptoError)
import           Data.Aeson                   (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import qualified Data.ByteArray               as BA
import qualified Data.ByteString              as BSS
import qualified Data.ByteString.Lazy         as BSL
import           Data.Swagger.Internal.Schema (ToSchema)
import           GHC.Generics                 (Generic)
import           KeyBytes                     (KeyBytes (..))
import           Language.PlutusTx.Lift       (makeLift)
import           Ledger.TxId

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

-- | A message with a cryptographic signature.
-- NOTE: relies on incorrect notion of signatures
newtype Signature = Signature { getSignature :: KeyBytes }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON)
    deriving newtype (Serialise)

makeLift ''Signature

-- | Check whether the given 'Signature' was signed by the private key corresponding to the given public key.
signedBy :: Signature -> PubKey -> TxId -> Bool
signedBy (Signature s) (PubKey k) txId =
    let k' = ED25519.publicKey $ BSL.toStrict $ getKeyBytes k
        s' = ED25519.signature $ BSL.toStrict $ getKeyBytes s
    in throwCryptoError $ ED25519.verify <$> k' <*> pure (getTxId txId) <*> s' -- TODO: is this what we want

-- | Sign the hash of a transaction using a private key.
sign :: TxId -> PrivateKey -> Signature
sign (TxIdOf txId) (PrivateKey privKey) =
    let k  = ED25519.secretKey $ BSL.toStrict $ getKeyBytes privKey
        pk = ED25519.toPublic <$> k
        salt :: BSS.ByteString
        salt = "" -- TODO: do we need better salt?
        convert = Signature . KeyBytes . BSL.pack . BA.unpack
    in throwCryptoError $ fmap convert (ED25519.sign <$> k <*> pure salt <*> pk <*> pure txId)

