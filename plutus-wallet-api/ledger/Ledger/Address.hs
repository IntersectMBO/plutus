{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE DerivingVia    #-}
module Ledger.Address (
    -- Note that the constructor is not exported - generally people shouldn't be able
    -- to look inside addresses
    Address,
    pubKeyAddress,
    scriptAddress,
    scriptHashAddress,
    unsafeGetAddress
    ) where

import qualified Codec.CBOR.Write          as Write
import           Codec.Serialise.Class     (Serialise, encode)
import           Crypto.Hash               (Digest, SHA256, hash)
import           Data.Aeson                (FromJSON, FromJSONKey (..), ToJSON, ToJSONKey (..))
import qualified Data.ByteArray            as BA
import qualified Data.ByteString.Lazy      as BSL
import           Data.String               (IsString(..))
import           Data.Hashable             (Hashable, hashWithSalt)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics              (Generic)
import           IOTS                      (IotsType)

import           LedgerBytes               (LedgerBytes(..))
import           Ledger.Crypto
import           Ledger.Orphans            ()
import           Ledger.Scripts

-- | A payment address using a hash as the id.
newtype Address = Address { getAddress :: BSL.ByteString }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON, ToJSONKey, FromJSONKey, IotsType)
    deriving newtype (Serialise)
    deriving (IsString) via LedgerBytes
    deriving Pretty via LedgerBytes

instance Hashable Address where
    hashWithSalt s (Address digest) = hashWithSalt s $ BSL.unpack digest

-- | The address that should be targeted by a transaction output locked by the given public key.
pubKeyAddress :: PubKey -> Address
pubKeyAddress pk = Address $ BSL.fromStrict $ BA.convert h' where
    h :: Digest SHA256 = hash $ Write.toStrictByteString e
    h' :: Digest SHA256 = hash h
    e = encode pk

-- | The address that should be used by a transaction output locked by the given validator script.
scriptAddress :: Validator -> Address
scriptAddress vl = Address hsh where
    (ValidatorHash hsh) = validatorHash vl

-- | The address that should be used by a transaction output locked by the given validator script.
scriptHashAddress :: ValidatorHash -> Address
scriptHashAddress vh = Address hsh where
    (ValidatorHash hsh) = vh

-- | This function should not exist, and is only here transitionally. We need it to construct
-- 'PendingTx', but this is because 'PendingTx' currently reveals too much information about
-- what is in addresses.
unsafeGetAddress :: Address -> BSL.ByteString
unsafeGetAddress (Address h) = h
