{-# OPTIONS_GHC -Wno-orphans #-}

module Ledger.Arbitrary where

import           Ledger.Oracle
import           Plutus.V1.Ledger.Arbitrary        ()

import           Test.QuickCheck.Arbitrary.Generic (Arbitrary (arbitrary, shrink), genericArbitrary, genericShrink)

instance Arbitrary (SignedMessage a) where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary a => Arbitrary (Observation a) where
  arbitrary = genericArbitrary
  shrink = genericShrink
