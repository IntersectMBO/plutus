{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module Ledger.Address (
    Address (..),
    pubKeyAddress,
    scriptAddress,
    scriptHashAddress,
    ) where

import           Codec.Serialise.Class     (Serialise)
import           Control.DeepSeq           (NFData)
import           Data.Aeson                (FromJSON, FromJSONKey (..), ToJSON, ToJSONKey (..))
import           Data.Hashable             (Hashable)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics              (Generic)
import           IOTS                      (IotsType)
import qualified Language.PlutusTx         as PlutusTx
import qualified Language.PlutusTx.Eq      as PlutusTx

import           Ledger.Crypto
import           Ledger.Orphans            ()
import           Ledger.Scripts

-- | A payment address using a hash as the id.
data Address = PubKeyAddress PubKeyHash
    | ScriptAddress ValidatorHash
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON, ToJSONKey, FromJSONKey, IotsType, Serialise, Hashable, NFData)

instance Pretty Address where
    pretty (PubKeyAddress pkh) = "PubKeyAddress:" <+> pretty pkh
    pretty (ScriptAddress vh)  = "ScriptAddress:" <+> pretty vh

instance PlutusTx.Eq Address where
    PubKeyAddress pkh == PubKeyAddress pkh' = pkh PlutusTx.== pkh'
    ScriptAddress vh  == ScriptAddress vh'  = vh  PlutusTx.== vh'
    _ == _                                  = False

{-# INLINABLE pubKeyAddress #-}
-- | The address that should be targeted by a transaction output locked by the given public key.
pubKeyAddress :: PubKey -> Address
pubKeyAddress pk = PubKeyAddress $ pubKeyHash pk

-- | The address that should be used by a transaction output locked by the given validator script.
scriptAddress :: Validator -> Address
scriptAddress = ScriptAddress . validatorHash

-- | The address that should be used by a transaction output locked by the given validator script hash.
scriptHashAddress :: ValidatorHash -> Address
scriptHashAddress = ScriptAddress

PlutusTx.makeIsData ''Address
PlutusTx.makeLift ''Address
