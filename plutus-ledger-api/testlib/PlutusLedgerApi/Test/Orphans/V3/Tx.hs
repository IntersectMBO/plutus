{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DerivingVia #-}

module PlutusLedgerApi.Test.Orphans.V3.Tx () where

import Data.Coerce (coerce)
import PlutusLedgerApi.Test.Orphans.PlutusTx (Blake2b256Hash (Blake2b256Hash))
import PlutusLedgerApi.V3.Tx (TxId (TxId), TxOutRef (TxOutRef))
import Test.QuickCheck (Arbitrary (arbitrary, shrink), CoArbitrary (coarbitrary),
                        Function (function), NonNegative (NonNegative), functionMap, getNonNegative)

-- | BLAKE2b-256 hash (32 bytes) of a transaction ID.
deriving via Blake2b256Hash instance Arbitrary TxId

deriving via Blake2b256Hash instance CoArbitrary TxId

instance Function TxId where
  {-# INLINEABLE function #-}
  function = functionMap coerce TxId


instance Arbitrary TxOutRef where
  {-# INLINEABLE arbitrary #-}
  arbitrary = TxOutRef <$> arbitrary <*> (getNonNegative <$> arbitrary)

  {-# INLINEABLE shrink #-}
  shrink (TxOutRef tid ix) =
    TxOutRef <$> shrink tid <*> (fmap getNonNegative . shrink . NonNegative $ ix)

instance CoArbitrary TxOutRef where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (TxOutRef tid ix) =
    coarbitrary tid . coarbitrary ix

instance Function TxOutRef where
  {-# INLINEABLE function #-}
  function = functionMap (\(TxOutRef tid ix) -> (tid, ix)) (uncurry TxOutRef)
