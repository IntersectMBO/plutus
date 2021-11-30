{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- Prevent unboxing, which the plugin can't deal with
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}

-- | Functions for working with 'Value'.
module Plutus.V2.Ledger.Value(
    -- ** Currency symbols
      CurrencySymbol(..)
    , currencySymbol
    , mpsSymbol
    , currencyMPSHash
    -- ** Token names
    , TokenName(..)
    , tokenName
    , toString
    -- * Asset classes
    , AssetClass(..)
    , assetClass
    , assetClassValue
    , assetClassValueOf
    -- ** Value
    , Value(..)
    , singleton
    , valueOf
    , currencyValueOf
    , scale
    , symbols
      -- * Partial order operations
    , geq
    , gt
    , leq
    , lt
      -- * Etc.
    , isZero
    , split
    , unionWith
    , flattenValue
    ) where

import Plutus.V1.Ledger.Value
import PlutusTx.AssocMap qualified as Map
import PlutusTx.Maybe
import PlutusTx.Monoid

{-# INLINABLE currencyValueOf #-}
-- | Get the quantities of just the given 'CurrencySymbol' in the 'Value'.
currencyValueOf :: Value -> CurrencySymbol -> Value
currencyValueOf (Value m) c = case Map.lookup c m of
    Nothing -> mempty
    Just t  -> Value (Map.singleton c t)
