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

{- | Addresses and account identifiers for Plutus V4.

In Plutus V1-V3 an `Address` pairs a payment credential with an optional
staking credential. In V4 staking credentials no longer exist: the funds
locked by an address are staked via an account, identified by an `AccountId`.
-}
module PlutusLedgerApi.V4.Data.Address
  ( AccountId (..)
  , Address
  , pattern Address
  , pattern AddressProtected
  , matchAddress
  , addressCredential
  , addressStakingAccountId
  , pubKeyHashAddress
  , toPubKeyHash
  , toScriptHash
  , scriptHashAddress
  , stakingAccountId
  , isProtectedAddress
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

{- | An address may contain two things: the payment credential, and optionally
the 'AccountId' of the account the funds are staked to.
-}
PlutusTx.asData
  [d|
    data Address
      = Address Credential (Maybe AccountId)
      | AddressProtected Credential (Maybe AccountId)
      deriving stock (Eq, Ord, Show, Generic)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.deriveEq ''Address

{-# INLINEABLE addressCredential #-}
addressCredential :: Address -> Credential
addressCredential (Address c _) = c
addressCredential (AddressProtected c _) = c

{-# INLINEABLE addressStakingAccountId #-}
addressStakingAccountId :: Address -> Maybe AccountId
addressStakingAccountId (Address _ account) = account
addressStakingAccountId (AddressProtected _ account) = account

instance Pretty Address where
  pretty (Address cred accountId) =
    let staking = maybe "no staking account" pretty accountId
     in pretty cred <+> parens staking
  pretty (AddressProtected cred accountId) =
    "protected" <+> pretty (Address cred accountId)

{-# INLINEABLE pubKeyHashAddress #-}

{- | The address that should be targeted by a transaction output
locked by the public key with the given hash.
-}
pubKeyHashAddress :: PubKeyHash -> Address
pubKeyHashAddress pkh = Address (PubKeyCredential pkh) Nothing

{-# INLINEABLE toPubKeyHash #-}

-- | The PubKeyHash of the address, if any
toPubKeyHash :: Address -> Maybe PubKeyHash
toPubKeyHash (Address (PubKeyCredential k) _) = Just k
toPubKeyHash (AddressProtected (PubKeyCredential k) _) = Just k
toPubKeyHash _ = Nothing

{-# INLINEABLE toScriptHash #-}

-- | The validator hash of the address, if any
toScriptHash :: Address -> Maybe ScriptHash
toScriptHash (Address (ScriptCredential k) _) = Just k
toScriptHash (AddressProtected (ScriptCredential k) _) = Just k
toScriptHash _ = Nothing

{-# INLINEABLE scriptHashAddress #-}

{- | The address that should be used by a transaction output
locked by the given validator script hash.
-}
scriptHashAddress :: ScriptHash -> Address
scriptHashAddress vh = Address (ScriptCredential vh) Nothing

{-# INLINEABLE stakingAccountId #-}

-- | The account the funds locked by an address are staked to (if any)
stakingAccountId :: Address -> Maybe AccountId
stakingAccountId (Address _ a) = a
stakingAccountId (AddressProtected _ a) = a

-- | Whether creation of an output at this address requires recipient authorization.
{-# INLINEABLE isProtectedAddress #-}
isProtectedAddress :: Address -> Bool
isProtectedAddress Address {} = False
isProtectedAddress AddressProtected {} = True

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(PlutusTx.makeLift ''Address)
