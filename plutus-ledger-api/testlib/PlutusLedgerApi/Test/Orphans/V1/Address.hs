{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.Orphans.V1.Address () where

import PlutusLedgerApi.Test.Orphans.V1.Credential ()
import PlutusLedgerApi.V1.Address (Address (Address))
import PlutusLedgerApi.V1.Credential (Credential, StakingCredential)
import Test.QuickCheck (Arbitrary (arbitrary, shrink), CoArbitrary (coarbitrary),
                        Function (function), functionMap)

instance Arbitrary Address where
  {-# INLINEABLE arbitrary #-}
  arbitrary = Address <$> arbitrary <*> arbitrary

  {-# INLINEABLE shrink #-}
  -- As Credential does not shrink, we just pass it through.
  shrink (Address cred scred) = Address cred <$> shrink scred

instance CoArbitrary Address where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (Address cred scred) =
    coarbitrary cred . coarbitrary scred

instance Function Address where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into :: Address -> (Credential, Maybe StakingCredential)
      into (Address cred scred) = (cred, scred)

      outOf :: (Credential, Maybe StakingCredential) -> Address
      outOf (cred, scred) = Address cred scred

