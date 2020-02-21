{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE OverloadedStrings #-}
module Ledger.Address (
    Address (..),
    pubKeyAddress,
    scriptAddress,
    scriptHashAddress,
    ) where

import           Codec.Serialise.Class     (Serialise)
import           Data.Aeson                (FromJSON, FromJSONKey (..), ToJSON, ToJSONKey (..))
import           Data.Hashable             (Hashable)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics              (Generic)
import           IOTS                      (IotsType)

import           Ledger.Crypto
import           Ledger.Orphans            ()
import           Ledger.Scripts

-- | A payment address using a hash as the id.
data Address = PubKeyAddress PubKeyHash
    | ScriptAddress ValidatorHash
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON, ToJSONKey, FromJSONKey, IotsType, Serialise, Hashable)

instance Pretty Address where
    pretty (PubKeyAddress pkh) = "PubKeyAddress:" <+> pretty pkh
    pretty (ScriptAddress vh)  = "ScriptAddress:" <+> pretty vh

-- | The address that should be targeted by a transaction output locked by the given public key.
pubKeyAddress :: PubKey -> Address
pubKeyAddress pk = PubKeyAddress $ pubKeyHash pk

-- | The address that should be used by a transaction output locked by the given validator script.
scriptAddress :: Validator -> Address
scriptAddress = ScriptAddress . validatorHash

-- | The address that should be used by a transaction output locked by the given validator script hash.
scriptHashAddress :: ValidatorHash -> Address
scriptHashAddress = ScriptAddress
