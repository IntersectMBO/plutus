{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin
    -fno-ignore-interface-pragmas
    -fno-omit-interface-pragmas
    -fno-full-laziness
    -fno-spec-constr
    -fno-specialise
    -fno-strictness
    -fno-unbox-strict-fields
    -fno-unbox-small-strict-fields #-}

module PlutusBenchmark.LinearVesting where

import PlutusTx.Prelude

import PlutusLedgerApi.Data.V3 (Address, Datum (..), ScriptContext, scriptContextScriptInfo)
import PlutusLedgerApi.V1.Value (AssetClass)
import PlutusLedgerApi.V3.Data.Contexts (pattern SpendingScript)
import PlutusTx (CompiledCode, compile, makeIsDataIndexed, makeLift)
import Prelude qualified as Haskell

data VestingDatum = VestingDatum
  { beneficiary              :: Address
  , vestingAsset             :: AssetClass
  , totalVestingQty          :: Integer
  , vestingPeriodStart       :: Integer
  , vestingPeriodEnd         :: Integer
  , firstUnlockPossibleAfter :: Integer
  , totalInstallments        :: Integer
  }
  deriving stock (Haskell.Show)

$(makeLift ''VestingDatum)
$(makeIsDataIndexed ''VestingDatum [('VestingDatum, 0)])

data VestingRedeemer
  = PartialUnlock
  | FullUnlock

$(PlutusTx.makeLift ''VestingRedeemer)
$( PlutusTx.makeIsDataIndexed
     ''VestingRedeemer
     [('PartialUnlock, 0), ('FullUnlock, 1)]
 )

{-# INLINEABLE untypedValidator #-}
untypedValidator :: BuiltinData -> CompiledCode BuiltinUnit
untypedValidator scriptContextData =
  $$(compile [||check (typedValidator scriptContext)||])
 where
  scriptContext :: ScriptContext = unsafeFromBuiltinData scriptContextData

{-# INLINEABLE typedValidator #-}
typedValidator :: ScriptContext -> Bool
typedValidator ctx = totalInstallments datum > 0
 where
  {-# INLINEABLE datum #-}
  datum :: VestingDatum
  datum =
    case scriptContextScriptInfo ctx of
      SpendingScript _outRef (Just (Datum d)) -> unsafeFromBuiltinData d
      _                                       -> error ()
