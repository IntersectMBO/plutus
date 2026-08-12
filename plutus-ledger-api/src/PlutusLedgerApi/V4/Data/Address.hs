{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
-- needed for asData pattern synonyms
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

{-| Addresses and account identifiers for Plutus V4.

In Plutus V1-V3 an `Address` pairs a payment credential with an optional
staking credential. In V4 staking credentials no longer exist: the funds
locked by an address are staked via an account, identified by an `AccountId`. -}
module PlutusLedgerApi.V4.Data.Address
  ( AccountId (..)
  , Address
  , pattern Address
  , matchAddress
  , addressCredential
  , addressStakingAccountId
  , pubKeyHashAddress
  , toPubKeyHash
  , toScriptHash
  , scriptHashAddress
  , stakingAccountId
  ) where

import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Crypto (PubKeyHash)
import PlutusLedgerApi.V1.Data.Credential
  ( Credential
  , pattern PubKeyCredential
  , pattern ScriptCredential
  )
import PlutusLedgerApi.V1.Scripts (ScriptHash)
import PlutusTx qualified
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Eq qualified as PlutusTx
import Prettyprinter (Pretty (pretty), parens, (<+>))
import Prettyprinter.Extras (PrettyShow (PrettyShow))

newtype AccountId = AccountId Credential
  deriving stock (Generic)
  deriving (Pretty) via (PrettyShow AccountId)
  deriving newtype
    ( Eq
    , Show
    , PlutusTx.Eq
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )

PlutusTx.makeLift ''AccountId

{-| An address may contain two things: the payment credential, and optionally
the 'AccountId' of the account the funds are staked to. -}
PlutusTx.asData
  [d|
    data Address = Address
      { addressCredential :: Credential
      , -- \^ the payment credential
        addressStakingAccountId :: Maybe AccountId
      }
      -- \^ the account the funds locked by this address are staked to

      deriving stock (Eq, Ord, Show, Generic)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.deriveEq ''Address

instance Pretty Address where
  pretty (Address cred accountId) =
    let staking = maybe "no staking account" pretty accountId
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

{-# INLINEABLE stakingAccountId #-}

-- | The account the funds locked by an address are staked to (if any)
stakingAccountId :: Address -> Maybe AccountId
stakingAccountId (Address _ a) = a

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(PlutusTx.makeLift ''Address)
