{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

module PlutusBenchmark.LinearVesting where

import PlutusTx.Prelude

import PlutusLedgerApi.V1.Value (AssetClass)
import PlutusLedgerApi.V3 (Address, Datum (..), ScriptContext, scriptContextScriptInfo)
import PlutusLedgerApi.V3.Contexts (pattern SpendingScript)
import PlutusTx (CompiledCode, compile, makeIsDataIndexed, makeLift)
import Prelude qualified as Haskell

import PlutusTx.Builtins.Internal qualified as BI

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

validatorCode :: CompiledCode (BuiltinData -> BuiltinUnit)
validatorCode = $$(compile [||untypedValidator||])

{-# INLINEABLE untypedValidator #-}
untypedValidator :: BuiltinData -> BuiltinUnit
untypedValidator _scriptContext = BI.unitval

{-# INLINEABLE typedValidator #-}
typedValidator :: ScriptContext -> Bool
typedValidator scriptContext = totalInstallments datum > 0
 where
  {-# INLINEABLE datum #-}
  datum :: VestingDatum
  datum =
    case scriptContextScriptInfo scriptContext of
      SpendingScript _outRef (Just (Datum d)) -> unsafeFromBuiltinData d
      _                                       -> error ()
