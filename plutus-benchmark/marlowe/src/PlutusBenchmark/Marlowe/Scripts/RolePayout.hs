
-- editorconfig-checker-disable-file


-----------------------------------------------------------------------------
--
-- Module      :  $Headers
-- License     :  Apache 2.0
--
-- Stability   :  Experimental
-- Portability :  Portable
--
-- | Marlowe validators.
--
-----------------------------------------------------------------------------


{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.0.0 #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}


module PlutusBenchmark.Marlowe.Scripts.RolePayout
  (-- * Payout Validator
    rolePayoutValidatorHash
  , rolePayoutValidatorBytes
  , rolePayoutValidator
  , mkRolePayoutValidator
  ) where


import PlutusLedgerApi.V2 (CurrencySymbol, ScriptContext (scriptContextTxInfo), ScriptHash (..),
                           SerialisedScript, TokenName, serialiseCompiledCode)
import PlutusLedgerApi.V2.Contexts (valueSpent)
import PlutusTx (CompiledCode, unsafeFromBuiltinData)
import PlutusTx.Plugin ()
import PlutusTx.Prelude as PlutusTxPrelude (Bool (..), BuiltinData, check, toBuiltin, ($), (.))

import Cardano.Crypto.Hash qualified as Hash
import Data.ByteString qualified as BS
import Data.ByteString.Short qualified as SBS
import PlutusLedgerApi.V1.Value qualified as Val
import PlutusTx qualified


-- | Tag for the Marlowe payout validator.
data TypedRolePayoutValidator


-- | The Marlowe payout validator.
mkRolePayoutValidator :: (CurrencySymbol, TokenName)  -- ^ The datum is the currency symbol and role name for the payout.
                      -> ()                           -- ^ No redeemer is required.
                      -> ScriptContext                -- ^ The script context.
                      -> Bool                         -- ^ Whether the transaction validated.
mkRolePayoutValidator (currency, role) _ ctx =
    -- The role token for the correct currency must be present.
    -- [Marlowe-Cardano Specification: "17. Payment authorized".]
    Val.singleton currency role 1 `Val.leq` valueSpent (scriptContextTxInfo ctx)


-- | Compute the hash of a script.
hashScript :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ()) -> ScriptHash
hashScript =
  -- FIXME: Apparently this is the wrong recipe, since its hash disagrees with `cardano-cli`.
  ScriptHash
    . toBuiltin
    . (Hash.hashToBytes :: Hash.Hash Hash.Blake2b_224 SBS.ShortByteString -> BS.ByteString)
    . Hash.hashWith (BS.append "\x02" . SBS.fromShort)  -- For Plutus V2.
    . serialiseCompiledCode


{-# INLINABLE rolePayoutValidator #-}

-- | The Marlowe payout validator.
rolePayoutValidator :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
rolePayoutValidator =
  $$(PlutusTx.compile [|| rolePayoutValidator' ||])
    where
      rolePayoutValidator' :: BuiltinData -> BuiltinData -> BuiltinData -> ()
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
