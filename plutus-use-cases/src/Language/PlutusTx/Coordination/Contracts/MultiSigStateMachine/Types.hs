{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine.Types where

import           Ledger.Slot               (Slot)
import           Ledger.Value              (Value)
import           Wallet

import qualified Language.PlutusTx         as PlutusTx
import           Language.PlutusTx.Prelude

-- | A proposal for making a payment under the multisig scheme.
data Payment = Payment
    { paymentAmount    :: Value
    -- ^ How much to pay out
    , paymentRecipient :: PubKey
    -- ^ Address to pay the value to
    , paymentDeadline  :: Slot
    -- ^ Time until the required amount of signatures has to be collected.
    }

instance Eq Payment where
    {-# INLINABLE (==) #-}
    (Payment vl pk sl) == (Payment vl' pk' sl') = vl == vl' && pk == pk' && sl == sl'

PlutusTx.makeLift ''Payment

data Params = Params
    { mspSignatories  :: [PubKey]
    -- ^ Public keys that are allowed to authorise payments
    , mspRequiredSigs :: Integer
    -- ^ How many signatures are required for a payment
    }

PlutusTx.makeLift ''Params

-- | State of the multisig contract.
data State =
    InitialState Value
    -- ^ Money is locked, anyone can make a proposal for a payment-

    | CollectingSignatures Value Payment [PubKey]
    -- ^ A payment has been proposed and is awaiting signatures.

-- Needs to be in a different file due to #978
instance Eq State where
    {-# INLINABLE (==) #-}
    (InitialState v) == (InitialState v') = v == v'
    (CollectingSignatures vl pmt pks) == (CollectingSignatures vl' pmt' pks') =
        vl == vl' && pmt == pmt' && pks == pks'
    _ == _ = False

PlutusTx.makeLift ''State

data Input =
    ProposePayment Payment
    -- ^ Propose a payment. The payment can be made as soon as enough
    --   signatures have been collected.

    | AddSignature PubKey
    -- ^ Add a signature to the sigs. that have been collected for the
    --   current proposal.

    | Cancel
    -- ^ Cancel the current proposal if the deadline has passed

    | Pay
    -- ^ Make the payment.

PlutusTx.makeLift ''Input
