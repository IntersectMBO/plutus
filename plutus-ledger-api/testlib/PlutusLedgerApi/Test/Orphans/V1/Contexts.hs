{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.Orphans.V1.Contexts () where

import Data.Set qualified as Set
import PlutusLedgerApi.Test.Orphans.V1.DCert ()
import PlutusLedgerApi.Test.Orphans.V1.Interval ()
import PlutusLedgerApi.Test.Orphans.V1.Tx ()
import PlutusLedgerApi.Test.Orphans.V1.Value qualified as Value
import PlutusLedgerApi.V1.Contexts (ScriptContext (ScriptContext),
                                    ScriptPurpose (Certifying, Minting, Rewarding, Spending),
                                    TxInInfo (TxInInfo), TxInfo (TxInfo))
import PlutusLedgerApi.V1.Credential (StakingCredential)
import PlutusLedgerApi.V1.Crypto (PubKeyHash)
import PlutusLedgerApi.V1.DCert (DCert)
import PlutusLedgerApi.V1.Scripts (Datum, DatumHash)
import PlutusLedgerApi.V1.Time (POSIXTimeRange)
import PlutusLedgerApi.V1.Tx (TxId, TxOut, TxOutRef)
import PlutusLedgerApi.V1.Value (CurrencySymbol, Value)
import Test.QuickCheck (Arbitrary (arbitrary, shrink), CoArbitrary (coarbitrary),
                        Function (function), NonEmptyList (NonEmpty), functionMap, getNonEmpty,
                        oneof, variant)

instance Arbitrary ScriptContext where
  {-# INLINEABLE arbitrary #-}
  arbitrary = ScriptContext <$> arbitrary <*> arbitrary

  {-# INLINEABLE shrink #-}
  shrink (ScriptContext tinfo p) =
    [ScriptContext tinfo' p | tinfo' <- shrink tinfo] ++
    [ScriptContext tinfo p' | p' <- shrink p]

instance CoArbitrary ScriptContext where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (ScriptContext tinfo p) =
    coarbitrary tinfo . coarbitrary p

instance Function ScriptContext where
  {-# INLINEABLE function #-}
  function =
    functionMap
      (\(ScriptContext tinfo p) -> (tinfo, p))
      (uncurry ScriptContext)


instance Arbitrary TxInInfo where
  {-# INLINEABLE arbitrary #-}
  arbitrary = TxInInfo <$> arbitrary <*> arbitrary

  {-# INLINEABLE shrink #-}
  shrink (TxInInfo outref resolved) =
        [TxInInfo outref' resolved | outref' <- shrink outref] ++
        [TxInInfo outref resolved' | resolved' <- shrink resolved]

instance CoArbitrary TxInInfo where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (TxInInfo outref resolved) =
    coarbitrary outref . coarbitrary resolved

instance Function TxInInfo where
  {-# INLINEABLE function #-}
  function =
    functionMap
      (\(TxInInfo outref resolved) -> (outref, resolved))
      (uncurry TxInInfo)


instance Arbitrary TxInfo where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    TxInfo . getNonEmpty
      <$> arbitrary -- inputs
      <*> (getNonEmpty <$> arbitrary) -- outputs
      <*> (Value.getFeeValue <$> arbitrary) -- fee
      <*> (Value.getMintValue <$> arbitrary) -- mint
      <*> arbitrary -- dcert
      <*> arbitrary -- withdrawals
      <*> arbitrary -- valid time range
      <*> (Set.toList <$> arbitrary) -- signatories
      <*> arbitrary -- data
      <*> arbitrary -- tid

  {-# INLINEABLE shrink #-}
  shrink (TxInfo ins outs fee mint dcert wdrl validRange sigs dats tid) =
    [ TxInfo ins' outs fee mint dcert wdrl validRange sigs dats tid
    | NonEmpty ins' <- shrink (NonEmpty ins) ] ++
    [ TxInfo ins outs' fee mint dcert wdrl validRange sigs dats tid
    | NonEmpty outs' <- shrink (NonEmpty outs) ] ++
    [ TxInfo ins outs fee' mint dcert wdrl validRange sigs dats tid
    | Value.FeeValue fee' <- shrink (Value.FeeValue fee) ] ++
    [ TxInfo ins outs fee mint' dcert wdrl validRange sigs dats tid
    | Value.MintValue mint' <- shrink (Value.MintValue mint) ] ++
    [ TxInfo ins outs fee mint dcert' wdrl validRange sigs dats tid
    | dcert' <- shrink dcert ] ++
    [ TxInfo ins outs fee mint dcert wdrl' validRange sigs dats tid
    | wdrl' <- shrink wdrl ] ++
    [ TxInfo ins outs fee mint dcert wdrl validRange' sigs dats tid
    | validRange' <- shrink validRange ] ++
    [ TxInfo ins outs fee mint dcert wdrl validRange sigs' dats tid
    | sigs' <- Set.toList <$> shrink (Set.fromList sigs) ] ++
    [ TxInfo ins outs fee mint dcert wdrl validRange sigs dats' tid
    | dats' <- shrink dats ] ++
    [ TxInfo ins outs fee mint dcert wdrl validRange sigs dats tid'
    | tid' <- shrink tid ]

instance CoArbitrary TxInfo where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (TxInfo ins outs fee mint dcert wdrl validRange sigs dats tid) =
    coarbitrary ins
      . coarbitrary outs
      . coarbitrary fee
      . coarbitrary mint
      . coarbitrary dcert
      . coarbitrary wdrl
      . coarbitrary validRange
      . coarbitrary sigs
      . coarbitrary dats
      . coarbitrary tid

instance Function TxInfo where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      -- We have to nest tuples as Function doesn't have instances for anything
      -- bigger than a 6-tuple.
      into ::
        TxInfo ->
        ([TxInInfo]
        , [TxOut]
        , Value
        , Value
        , [DCert]
        , ( [(StakingCredential, Integer)]
          , POSIXTimeRange, [PubKeyHash]
          , [(DatumHash, Datum)]
          , TxId))
      into (TxInfo ins outs fee mint dcert wdrl validRange sigs dats tid) =
        (ins, outs, fee, mint, dcert, (wdrl, validRange, sigs, dats, tid))

      outOf ::
        ([TxInInfo]
        , [TxOut]
        , Value
        , Value
        , [DCert]
        , ( [(StakingCredential, Integer)]
          , POSIXTimeRange, [PubKeyHash]
          , [(DatumHash, Datum)]
          , TxId)) ->
        TxInfo
      outOf (ins, outs, fee, mint, dcert, (wdrl, validRange, sigs, dats, tid)) =
        TxInfo ins outs fee mint dcert wdrl validRange sigs dats tid


instance Arbitrary ScriptPurpose where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    oneof
      [ Minting <$> arbitrary
      , Spending <$> arbitrary
      , Rewarding <$> arbitrary
      , Certifying <$> arbitrary
      ]

  {-# INLINEABLE shrink #-}
  shrink = \case
    Minting cs -> Minting <$> shrink cs
    Spending txo -> Spending <$> shrink txo
    Rewarding scred -> Rewarding <$> shrink scred
    Certifying dcert -> Certifying <$> shrink dcert

instance CoArbitrary ScriptPurpose where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    Minting cs -> variant (0 :: Int) . coarbitrary cs
    Spending txo -> variant (1 :: Int) . coarbitrary txo
    Rewarding scred -> variant (2 :: Int) . coarbitrary scred
    Certifying dcert -> variant (3 :: Int) . coarbitrary dcert

instance Function ScriptPurpose where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        ScriptPurpose ->
        Either CurrencySymbol (Either TxOutRef (Either StakingCredential DCert))
      into = \case
        Minting cs -> Left cs
        Spending txo -> Right (Left txo)
        Rewarding scred -> Right (Right (Left scred))
        Certifying dcert -> Right (Right (Right dcert))

      outOf ::
        Either CurrencySymbol (Either TxOutRef (Either StakingCredential DCert)) ->
        ScriptPurpose
      outOf = \case
        Left cs -> Minting cs
        Right (Left txo) -> Spending txo
        Right (Right (Left scred)) -> Rewarding scred
        Right (Right (Right dcert)) -> Certifying dcert
