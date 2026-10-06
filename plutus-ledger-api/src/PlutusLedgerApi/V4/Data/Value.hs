{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module PlutusLedgerApi.V4.Data.Value
  ( module Value
  , AssetClass (..)
  , assetClass
  , assetClassValue
  , assetClassValueOf
  ) where

import Control.DeepSeq (NFData)
import Data.Data (Data)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Data.Value as Value hiding
  ( AssetClass (..)
  , assetClass
  , assetClassValue
  , assetClassValueOf
  )
import PlutusLedgerApi.V4.Internal (ListEncoded (..))
import PlutusTx qualified
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition (..), UnrollAll)
import PlutusTx.Prelude qualified as PlutusTx
import Prettyprinter.Extras (Pretty, PrettyShow (..))

newtype AssetClass = AssetClass {unAssetClass :: (CurrencySymbol, TokenName)}
  deriving stock (Generic, Data)
  deriving newtype (Eq, Ord, Show, NFData, PlutusTx.Eq, PlutusTx.Ord)
  deriving (Pretty) via PrettyShow (CurrencySymbol, TokenName)
  deriving
    (PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    via ListEncoded (CurrencySymbol, TokenName)

instance HasBlueprintDefinition AssetClass where
  type Unroll AssetClass = AssetClass ': UnrollAll '[CurrencySymbol, TokenName]

instance
  HasBlueprintSchema (CurrencySymbol, TokenName) referencedTypes
  => HasBlueprintSchema AssetClass referencedTypes
  where
  schema = schema @(ListEncoded (CurrencySymbol, TokenName)) @referencedTypes

PlutusTx.makeLift ''AssetClass

{-# INLINEABLE assetClass #-}
assetClass :: CurrencySymbol -> TokenName -> AssetClass
assetClass currency token = AssetClass (currency, token)

{-# INLINEABLE assetClassValue #-}
assetClassValue :: AssetClass -> Integer -> Value
assetClassValue (AssetClass (currency, token)) = singleton currency token

{-# INLINEABLE assetClassValueOf #-}
assetClassValueOf :: Value -> AssetClass -> Integer
assetClassValueOf value (AssetClass (currency, token)) = valueOf value currency token
