{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

-- | Address and staking address credentials for outputs.
module PlutusLedgerApi.V1.Data.Credential
  ( StakingCredential
  , pattern StakingHash
  , pattern StakingPtr
  , Credential
  , pattern PubKeyCredential
  , pattern ScriptCredential
  ) where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Crypto (PubKeyHash)
import PlutusLedgerApi.V1.Scripts (ScriptHash)
import PlutusTx qualified
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Blueprint (HasBlueprintDefinition)
import PlutusTx.Eq qualified as PlutusTx
import PlutusTx.Show (deriveShow)
import Prettyprinter (Pretty (..), (<+>))

{-| Credentials required to unlock a transaction output.

The 'PubKeyCredential' constructor represents the transaction that
spends this output and must be signed by the private key.
See `Crypto.PubKeyHash`.

The 'ScriptCredential' constructor represents the transaction that spends
this output must include the validator script and
be accepted by the validator. See `ScriptHash`. -}
PlutusTx.asData
  [d|
    data Credential
      = PubKeyCredential PubKeyHash
      | ScriptCredential ScriptHash
      deriving stock (Eq, Ord, Show, Generic)
      deriving anyclass (NFData, HasBlueprintDefinition)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.deriveEq ''Credential

instance Pretty Credential where
  pretty (PubKeyCredential pkh) = "PubKeyCredential:" <+> pretty pkh
  pretty (ScriptCredential val) = "ScriptCredential:" <+> pretty val

{-| Staking credential used to assign rewards.

The staking hash constructor is the `Credential` required to unlock a
transaction output. Either a public key credential (`Crypto.PubKeyHash`) or
a script credential (`ScriptHash`). Both are hashed with /BLAKE2b-244/. 28 byte.

The 'StakingPtr' constructor is the certificate pointer, constructed by the given
slot number, transaction and certificate indices.
NB: The fields should really be all `Word64`, as they are implemented in `Word64`,
but 'Integer' is our only integral type so we need to use it instead. -}
PlutusTx.asData
  [d|
    data StakingCredential
      = StakingHash Credential
      | StakingPtr
          Integer
          -- \^ the slot number
          Integer
          -- \^ the transaction index (within the block)
          Integer
      -- \^ the certificate index (within the transaction)
      deriving stock (Eq, Ord, Show, Generic)
      deriving anyclass (NFData, HasBlueprintDefinition)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.deriveEq ''StakingCredential

instance Pretty StakingCredential where
  pretty (StakingHash h) = "StakingHash" <+> pretty h
  pretty (StakingPtr a b c) = "StakingPtr:" <+> pretty a <+> pretty b <+> pretty c

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

PlutusTx.makeLift ''Credential
PlutusTx.makeLift ''StakingCredential

deriveShow ''Credential
deriveShow ''StakingCredential
