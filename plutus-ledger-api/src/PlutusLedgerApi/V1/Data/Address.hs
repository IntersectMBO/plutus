{-# LANGUAGE BangPatterns #-}
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

module PlutusLedgerApi.V1.Data.Address
  ( Address
  , pattern Address
  , addressCredential
  , addressStakingCredential
  , pubKeyHashAddress
  , toPubKeyHash
  , toScriptHash
  , scriptHashAddress
  , stakingCredential
  ) where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Crypto (PubKeyHash)
import PlutusLedgerApi.V1.Data.Credential
  ( Credential
  , StakingCredential
  , pattern PubKeyCredential
  , pattern ScriptCredential
  )
import PlutusLedgerApi.V1.Scripts (ScriptHash)
import PlutusTx qualified
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition)
import PlutusTx.Eq qualified as PlutusTx
import Prettyprinter (Pretty (pretty), parens, (<+>))

{-| An address may contain two credentials,
the payment credential and optionally a 'StakingCredential'. -}
PlutusTx.asData
  [d|
    data Address = Address
      { addressCredential :: Credential
      , -- \^ the payment credential
        addressStakingCredential :: Maybe StakingCredential
      }
      -- \^ the staking credential

      deriving stock (Eq, Ord, Show, Generic)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving anyclass (NFData, HasBlueprintDefinition)
    |]

PlutusTx.deriveEq ''Address

instance Pretty Address where
  pretty (Address cred stakingCred) =
    let staking = maybe "no staking credential" pretty stakingCred
     in pretty cred <+> parens staking

{-# INLINEABLE pubKeyHashAddress #-}

{-| The address that should be targeted by a transaction output
locked by the public key with the given hash. -}
pubKeyHashAddress :: PubKeyHash -> Address
pubKeyHashAddress pkh = Address (PubKeyCredential pkh) Nothing

{-# INLINEABLE toPubKeyHash #-}

-- | The PubKeyHash of the address, if any
toPubKeyHash :: Address -> Maybe PubKeyHash
toPubKeyHash (Address (PubKeyCredential k) _) = Just k
toPubKeyHash _ = Nothing

{-# INLINEABLE toScriptHash #-}

-- | The validator hash of the address, if any
toScriptHash :: Address -> Maybe ScriptHash
toScriptHash (Address (ScriptCredential k) _) = Just k
toScriptHash _ = Nothing

{-# INLINEABLE scriptHashAddress #-}

{-| The address that should be used by a transaction output
locked by the given validator script hash. -}
scriptHashAddress :: ScriptHash -> Address
scriptHashAddress vh = Address (ScriptCredential vh) Nothing

{-# INLINEABLE stakingCredential #-}

-- | The staking credential of an address (if any)
stakingCredential :: Address -> Maybe StakingCredential
stakingCredential (Address _ s) = s

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(PlutusTx.makeLift ''Address)
