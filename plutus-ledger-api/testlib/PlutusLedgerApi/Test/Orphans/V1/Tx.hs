{-# LANGUAGE DerivingVia #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.Orphans.V1.Tx () where

import Data.Coerce (coerce)
import PlutusLedgerApi.Test.Orphans.PlutusTx (Blake2b256Hash (Blake2b256Hash))
import PlutusLedgerApi.Test.Orphans.V1.Address ()
import PlutusLedgerApi.Test.Orphans.V1.Value qualified as Value
import PlutusLedgerApi.V1.Address (Address)
import PlutusLedgerApi.V1.Scripts (DatumHash)
import PlutusLedgerApi.V1.Tx (TxId (TxId), TxOut (TxOut), TxOutRef (TxOutRef))
import PlutusLedgerApi.V1.Value (Value)
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
    [TxOutRef tid' ix | tid' <- shrink tid] ++
    [TxOutRef tid ix' | NonNegative ix' <- shrink (NonNegative ix)]

instance CoArbitrary TxOutRef where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (TxOutRef tid ix) =
    coarbitrary tid . coarbitrary ix

instance Function TxOutRef where
  {-# INLINEABLE function #-}
  function = functionMap (\(TxOutRef tid ix) -> (tid, ix)) (uncurry TxOutRef)


instance Arbitrary TxOut where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    TxOut
      <$> arbitrary -- address
      <*> (Value.getUtxoValue <$> arbitrary) -- value
      <*> arbitrary -- maybe datum hash

  {-# INLINEABLE shrink #-}
  shrink (TxOut addr val mdh) =
    [TxOut addr' val mdh | addr' <- shrink addr] ++
    [TxOut addr val' mdh | Value.UTxOValue val' <- shrink (Value.UTxOValue val)] ++
    [TxOut addr val mdh' | mdh' <- shrink mdh]

instance CoArbitrary TxOut where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (TxOut addr val mdh) =
    coarbitrary addr . coarbitrary val . coarbitrary mdh

instance Function TxOut where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into :: TxOut -> (Address, Value, Maybe DatumHash)
      into (TxOut addr val mdh) = (addr, val, mdh)
      outOf :: (Address, Value, Maybe DatumHash) -> TxOut
      outOf (addr, val, mdh) = TxOut addr val mdh
