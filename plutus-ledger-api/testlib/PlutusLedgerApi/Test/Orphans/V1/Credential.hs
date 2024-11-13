{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.Orphans.V1.Credential () where

import PlutusLedgerApi.Test.Common.QuickCheck.Utils (fromAsWord64)
import PlutusLedgerApi.Test.Orphans.V1.Crypto ()
import PlutusLedgerApi.Test.Orphans.V1.Scripts ()
import PlutusLedgerApi.V1.Credential (Credential (PubKeyCredential, ScriptCredential),
                                      StakingCredential (StakingHash, StakingPtr))
import PlutusLedgerApi.V1.Crypto (PubKeyHash)
import PlutusLedgerApi.V1.Scripts (ScriptHash)
import Test.QuickCheck (Arbitrary (arbitrary, shrink), CoArbitrary (coarbitrary),
                        Function (function), NonNegative (NonNegative), functionMap, oneof, variant)

{- | As 'Credential' is just a wrapper around a hash with a tag, shrinking
this type doesn't make much sense. Therefore we don't do it.
-}
instance Arbitrary Credential where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    oneof
      [ PubKeyCredential <$> arbitrary
      , ScriptCredential <$> arbitrary
      ]

  {-# INLINEABLE shrink #-}
  shrink = \case
    PubKeyCredential pkh -> PubKeyCredential <$> shrink pkh
    ScriptCredential sh -> ScriptCredential <$> shrink sh

instance CoArbitrary Credential where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    PubKeyCredential pkh -> variant (0 :: Int) . coarbitrary pkh
    ScriptCredential sh -> variant (1 :: Int) . coarbitrary sh

instance Function Credential where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into :: Credential -> Either PubKeyHash ScriptHash
      into = \case
        PubKeyCredential pkh -> Left pkh
        ScriptCredential sh -> Right sh

      outOf :: Either PubKeyHash ScriptHash -> Credential
      outOf = \case
        Left pkh -> PubKeyCredential pkh
        Right sh -> ScriptCredential sh


instance Arbitrary StakingCredential where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    oneof
      [ StakingHash <$> arbitrary
      , StakingPtr . fromAsWord64
          <$> arbitrary
          <*> (fromAsWord64 <$> arbitrary)
          <*> (fromAsWord64 <$> arbitrary)
      ]

  {-# INLINEABLE shrink #-}
  shrink = \case
    StakingHash cred -> StakingHash <$> shrink cred
    StakingPtr i j k ->
      [StakingPtr i' j k | NonNegative i' <- shrink (NonNegative i)] ++
      [StakingPtr i j' k | NonNegative j' <- shrink (NonNegative j)] ++
      [StakingPtr i j k' | NonNegative k' <- shrink (NonNegative k)]

instance CoArbitrary StakingCredential where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    StakingHash cred -> variant (0 :: Int) . coarbitrary cred
    StakingPtr i j k ->
      variant (1 :: Int) . coarbitrary i . coarbitrary j . coarbitrary k

instance Function StakingCredential where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into :: StakingCredential -> Either Credential (Integer, Integer, Integer)
      into = \case
        StakingHash cred -> Left cred
        StakingPtr i j k -> Right (i, j, k)

      outOf :: Either Credential (Integer, Integer, Integer) -> StakingCredential
      outOf = \case
        Left cred -> StakingHash cred
        Right (i, j, k) -> StakingPtr i j k

