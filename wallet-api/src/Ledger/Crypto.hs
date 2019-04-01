{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell    #-}
module Ledger.Crypto where

import           Codec.Serialise.Class        (Serialise)
import           Control.Newtype.Generics     (Newtype)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Swagger.Internal.Schema (ToSchema)
import           GHC.Generics                 (Generic)
import           Language.PlutusTx.Lift       (makeLift)

-- | A cryptographic public key.
newtype PubKey = PubKey { getPubKey :: Int }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON, Newtype)
    deriving newtype (Serialise)

makeLift ''PubKey

-- | A message with a cryptographic signature.
-- NOTE: relies on incorrect notion of signatures
newtype Signature = Signature { getSignature :: Int }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON)
    deriving newtype (Serialise)

makeLift ''Signature

-- | Check whether the given 'Signature' was signed by the private key corresponding to the given public key.
signedBy :: Signature -> PubKey -> Bool
signedBy (Signature k) (PubKey s) = k == s
