{-# LANGUAGE LambdaCase #-}

module PlutusLedgerApi.Test.V2.OutputDatum where

import PlutusLedgerApi.V2
import Test.QuickCheck

instance Arbitrary OutputDatum where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    oneof
      [ pure NoOutputDatum
      , OutputDatumHash <$> arbitrary
      , OutputDatum <$> arbitrary
      ]
  {-# INLINEABLE shrink #-}
  -- We only shrink the OutputDatum case, since the others wouldn't shrink
  -- anyway.
  shrink = \case
    OutputDatum d -> OutputDatum <$> shrink d
    _ -> []

instance CoArbitrary OutputDatum where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    NoOutputDatum -> variant (0 :: Int)
    OutputDatumHash dh -> variant (1 :: Int) . coarbitrary dh
    OutputDatum d -> variant (2 :: Int) . coarbitrary d
