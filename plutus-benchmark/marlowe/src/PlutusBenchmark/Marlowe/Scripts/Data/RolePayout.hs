-- editorconfig-checker-disable-file
-----------------------------------------------------------------------------
--
-- Module      :  $Headers
-- License     :  Apache 2.0
--
-- Stability   :  Experimental
-- Portability :  Portable
--
-----------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.0.0 #-}

-- | Marlowe validators.
module PlutusBenchmark.Marlowe.Scripts.Data.RolePayout
  ( -- * Payout Validator
    rolePayoutValidatorHash
  , rolePayoutValidatorBytes
  , rolePayoutValidator
  , mkRolePayoutValidator
  ) where

import PlutusLedgerApi.Data.V2 qualified as Data
import PlutusLedgerApi.V2
  ( CurrencySymbol
  , ScriptHash (..)
  , SerialisedScript
  , TokenName
  , serialiseCompiledCode
  )
import PlutusLedgerApi.V2.Data.Contexts qualified as Data
import PlutusTx (CompiledCode, unsafeFromBuiltinData)
import PlutusTx.Plugin ()
import PlutusTx.Prelude as PlutusTxPrelude
  ( Bool (..)
  , BuiltinData
  , BuiltinUnit
  , check
  , toBuiltin
  , ($)
  , (.)
  )

import Cardano.Crypto.Hash qualified as Hash
import Data.ByteString qualified as BS
import Data.ByteString.Short qualified as SBS
import PlutusLedgerApi.V1.Value qualified as Val
import PlutusTx qualified

-- | Tag for the Marlowe payout validator.
data TypedRolePayoutValidator

-- | The Marlowe payout validator.
mkRolePayoutValidator
  :: (CurrencySymbol, TokenName)
  -- ^ The datum is the currency symbol and role name for the payout.
  -> ()
  -- ^ No redeemer is required.
  -> Data.ScriptContext
  -- ^ The script context.
  -> Bool
  -- ^ Whether the transaction validated.
mkRolePayoutValidator (currency, role) _ ctx =
  let spent =
        PlutusTx.unsafeFromBuiltinData
          . PlutusTx.toBuiltinData
          . Data.valueSpent
          . Data.scriptContextTxInfo
          $ ctx
   in -- The role token for the correct currency must be present.
      -- [Marlowe-Cardano Specification: "17. Payment authorized".]
      Val.singleton currency role 1 `Val.leq` spent

-- | Compute the hash of a script.
hashScript :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> BuiltinUnit) -> ScriptHash
hashScript =
  -- FIXME: Apparently this is the wrong recipe, since its hash disagrees with `cardano-cli`.
  ScriptHash
    . toBuiltin
    . (Hash.hashToBytes :: Hash.Hash Hash.Blake2b_224 SBS.ShortByteString -> BS.ByteString)
    . Hash.hashWith (BS.append "\x02" . SBS.fromShort) -- For Plutus V2.
    . serialiseCompiledCode

{-# INLINEABLE rolePayoutValidator #-}

-- | The Marlowe payout validator.
rolePayoutValidator :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> BuiltinUnit)
rolePayoutValidator =
  $$(PlutusTx.compile [||rolePayoutValidator'||])
  where
    rolePayoutValidator' :: BuiltinData -> BuiltinData -> BuiltinData -> BuiltinUnit
    rolePayoutValidator' d r p =
      check
        $ mkRolePayoutValidator
          (unsafeFromBuiltinData d)
          (unsafeFromBuiltinData r)
          (unsafeFromBuiltinData p)

-- | The serialisation of the Marlowe payout validator.
rolePayoutValidatorBytes :: SerialisedScript
rolePayoutValidatorBytes = serialiseCompiledCode rolePayoutValidator

-- | The hash of the Marlowe payout validator.
rolePayoutValidatorHash :: ScriptHash
rolePayoutValidatorHash = hashScript rolePayoutValidator
