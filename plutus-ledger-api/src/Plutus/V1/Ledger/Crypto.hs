{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module Plutus.V1.Ledger.Crypto(
    PubKey(..)
    , PubKeyHash(..)
    , PrivateKey(..)
    , Signature(..)
    ) where

import           Codec.Serialise.Class     (Serialise)
import           Control.DeepSeq           (NFData)
import           Control.Newtype.Generics  (Newtype)
import           Data.Aeson                (FromJSON (parseJSON), FromJSONKey, FromJSONKeyFunction (FromJSONKeyValue),
                                            ToJSON (toJSON), ToJSONKey, ToJSONKeyFunction (ToJSONKeyValue),
                                            genericParseJSON, genericToJSON, (.:))
import qualified Data.Aeson                as JSON
import qualified Data.Aeson.Extras         as JSON
import           Data.Hashable             (Hashable)
import           Data.String
import           Data.Text.Prettyprint.Doc
import           GHC.Generics              (Generic)
import           Plutus.V1.Ledger.Bytes    (LedgerBytes (..))
import           Plutus.V1.Ledger.Orphans  ()
import qualified PlutusTx
import           PlutusTx.Lift             (makeLift)
import qualified PlutusTx.Prelude          as PlutusTx

-- | A cryptographic public key.
newtype PubKey = PubKey { getPubKey :: LedgerBytes }
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (Newtype, ToJSON, FromJSON, NFData)
    deriving newtype (PlutusTx.Eq, PlutusTx.Ord, Serialise, PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    deriving IsString via LedgerBytes
    deriving (Show, Pretty) via LedgerBytes
makeLift ''PubKey

instance ToJSONKey PubKey where
  toJSONKey = ToJSONKeyValue (genericToJSON JSON.defaultOptions) JSON.toEncoding

instance FromJSONKey PubKey where
  fromJSONKey = FromJSONKeyValue (genericParseJSON JSON.defaultOptions)

-- | The hash of a public key. This is frequently used to identify the public key, rather than the key itself.
newtype PubKeyHash = PubKeyHash { getPubKeyHash :: PlutusTx.BuiltinByteString }
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON, Newtype, ToJSONKey, FromJSONKey, NFData)
    deriving newtype (PlutusTx.Eq, PlutusTx.Ord, Serialise, Hashable, PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    deriving IsString via LedgerBytes
    deriving (Show, Pretty) via LedgerBytes
makeLift ''PubKeyHash

-- | A cryptographic private key.
newtype PrivateKey = PrivateKey { getPrivateKey :: LedgerBytes }
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON, Newtype, ToJSONKey, FromJSONKey)
    deriving newtype (PlutusTx.Eq, PlutusTx.Ord, Serialise, PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    deriving (Show, Pretty) via LedgerBytes
    deriving Hashable via PlutusTx.BuiltinByteString

makeLift ''PrivateKey

-- | A message with a cryptographic signature.
newtype Signature = Signature { getSignature :: PlutusTx.BuiltinByteString }
    deriving stock (Eq, Ord, Generic)
    deriving newtype (PlutusTx.Eq, PlutusTx.Ord, Serialise, NFData, PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    deriving (Show, Pretty) via LedgerBytes

instance ToJSON Signature where
  toJSON signature =
    JSON.object
      [ ( "getSignature"
        , JSON.String .
          JSON.encodeByteString .
          PlutusTx.fromBuiltin .
          getSignature $
          signature)
      ]

instance FromJSON Signature where
  parseJSON =
    JSON.withObject "Signature" $ \object -> do
      raw <- object .: "getSignature"
      bytes <- JSON.decodeByteString raw
      pure . Signature $ PlutusTx.toBuiltin $ bytes

makeLift ''Signature
