{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Plutus.V1.Ledger.Arbitrary where

import           Test.QuickCheck.Arbitrary.Generic (Arbitrary (arbitrary, shrink), genericArbitrary, genericShrink)
import           Test.QuickCheck.Instances         ()

import           Plutus.V1.Ledger.Api
import           Plutus.V1.Ledger.Crypto
import           Plutus.V1.Ledger.Slot
import           Plutus.V1.Ledger.Value
import           PlutusTx.Arbitrary                ()
import           PlutusTx.Prelude                  hiding (fmap, (<$>))

deriving newtype instance Arbitrary BuiltinData
deriving newtype instance Arbitrary CurrencySymbol
deriving newtype instance Arbitrary AssetClass
deriving newtype instance Arbitrary Datum
deriving newtype instance Arbitrary DatumHash
deriving newtype instance Arbitrary LedgerBytes
deriving newtype instance Arbitrary POSIXTime
deriving newtype instance Arbitrary PubKey
deriving newtype instance Arbitrary PubKeyHash
deriving newtype instance Arbitrary Signature
deriving newtype instance Arbitrary Slot
deriving newtype instance Arbitrary TokenName
deriving newtype instance Arbitrary TxId
deriving newtype instance Arbitrary ValidatorHash

--------------------------------------------------------------------------------
-- Generics.
-- Would like to have GenericArbitrary newtype from 0.2.0 for deriving-via on all of these

instance Arbitrary TxOutRef where
  arbitrary = genericArbitrary
  shrink = genericShrink


instance Arbitrary Value where
  arbitrary = Prelude.foldMap (uncurry3 singleton) <$> arbitrary @[(CurrencySymbol, TokenName, Integer)]
  shrink = fmap (Prelude.foldMap (uncurry3 singleton)) . shrink . flattenValue
