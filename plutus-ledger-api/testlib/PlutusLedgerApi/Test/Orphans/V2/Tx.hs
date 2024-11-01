{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.Orphans.V2.Tx () where

import PlutusLedgerApi.Test.Orphans.V1.Address ()
import PlutusLedgerApi.Test.Orphans.V1.Scripts ()
import PlutusLedgerApi.Test.Orphans.V1.Value qualified as Value
import PlutusLedgerApi.V1.Address (Address)
import PlutusLedgerApi.V1.Scripts (Datum, DatumHash, ScriptHash)
import PlutusLedgerApi.V1.Value (Value)
import PlutusLedgerApi.V2.Tx (OutputDatum (NoOutputDatum, OutputDatum, OutputDatumHash),
                              TxOut (TxOut))
import Test.QuickCheck (Arbitrary (arbitrary, shrink), CoArbitrary (coarbitrary),
                        Function (function), functionMap, oneof, variant)

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

instance Function OutputDatum where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into :: OutputDatum -> Maybe (Either DatumHash Datum)
      into = \case
        NoOutputDatum -> Nothing
        OutputDatumHash dh -> Just (Left dh)
        OutputDatum d -> Just (Right d)

      outOf :: Maybe (Either DatumHash Datum) -> OutputDatum
      outOf = \case
        Nothing -> NoOutputDatum
        Just (Left dh) -> OutputDatumHash dh
        Just (Right d) -> OutputDatum d


instance Arbitrary TxOut where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    TxOut
      <$> arbitrary
      <*> (Value.getUtxoValue <$> arbitrary)
      <*> arbitrary
      <*> arbitrary

  {-# INLINEABLE shrink #-}
  shrink (TxOut addr val od msh) =
    TxOut
      <$> shrink addr
      <*> (Value.getUtxoValue <$> shrink (Value.UTxOValue val))
      <*> shrink od
      <*> shrink msh

instance CoArbitrary TxOut where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (TxOut addr val od msh) =
    coarbitrary addr . coarbitrary val . coarbitrary od . coarbitrary msh

instance Function TxOut where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        TxOut ->
        (Address, Value, OutputDatum, Maybe ScriptHash)
      into (TxOut addr val od msh) = (addr, val, od, msh)

      outOf ::
        (Address, Value, OutputDatum, Maybe ScriptHash) ->
        TxOut
      outOf (addr, val, od, msh) = TxOut addr val od msh
