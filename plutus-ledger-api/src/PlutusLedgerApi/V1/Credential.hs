-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

-- | Address and staking address credentials for outputs.
module PlutusLedgerApi.V1.Credential
    ( StakingCredential(..)
    , Credential(..)
    ) where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Crypto (PubKeyHash)
import PlutusLedgerApi.V1.Scripts (ValidatorHash)
import PlutusTx qualified
import PlutusTx.Bool qualified as PlutusTx
import PlutusTx.Eq qualified as PlutusTx
import Prettyprinter (Pretty (..), (<+>))

-- | Staking credential used to assign rewards.
data StakingCredential
    -- | The staking hash is the `Credential` required to unlock a transaction output. Either
    -- a public key credential (`Crypto.PubKeyHash`) or
    -- a script credential (`Scripts.ValidatorHash`). Both are hashed with /BLAKE2b-244/. 28 byte.
    = StakingHash Credential
    -- | NB: The fields should really be `Word64` `Natural` `Natural`,
    -- but 'Integer' is our only integral type so we need to use it instead.
    | StakingPtr Integer Integer Integer
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

instance Pretty StakingCredential where
    pretty (StakingHash h)    = "StakingHash" <+> pretty h
    pretty (StakingPtr a b c) = "StakingPtr:" <+> pretty a <+> pretty b <+> pretty c

instance PlutusTx.Eq StakingCredential where
    {-# INLINABLE (==) #-}
    StakingHash l == StakingHash r = l PlutusTx.== r
    StakingPtr a b c == StakingPtr a' b' c' =
        a PlutusTx.== a'
        PlutusTx.&& b PlutusTx.== b'
        PlutusTx.&& c PlutusTx.== c'
    _ == _ = False

-- | Credentials required to unlock a transaction output.
data Credential
  =
    -- | The transaction that spends this output must be signed by the private key.
    -- Hashed with /BLAKE2b-244/. 28 byte. See `Crypto.PubKeyHash`.
    PubKeyCredential PubKeyHash
    -- | The transaction that spends this output must include the validator script and
    -- be accepted by the validator. Hashed with /BLAKE2b-244/. 28 byte. See `Scripts.ValidatorHash`.
  | ScriptCredential ValidatorHash
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

instance Pretty Credential where
    pretty (PubKeyCredential pkh) = "PubKeyCredential:" <+> pretty pkh
    pretty (ScriptCredential val) = "ScriptCredential:" <+> pretty val

instance PlutusTx.Eq Credential where
    {-# INLINABLE (==) #-}
    PubKeyCredential l == PubKeyCredential r  = l PlutusTx.== r
    ScriptCredential a == ScriptCredential a' = a PlutusTx.== a'
    _ == _                                    = False

PlutusTx.makeIsDataIndexed ''Credential [('PubKeyCredential,0), ('ScriptCredential,1)]
PlutusTx.makeIsDataIndexed ''StakingCredential [('StakingHash,0), ('StakingPtr,1)]
PlutusTx.makeLift ''Credential
PlutusTx.makeLift ''StakingCredential
