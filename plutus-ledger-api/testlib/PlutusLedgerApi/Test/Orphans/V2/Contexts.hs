{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.Orphans.V2.Contexts () where

import Data.Set qualified as Set
import PlutusLedgerApi.Test.Orphans.V1.Contexts ()
import PlutusLedgerApi.Test.Orphans.V1.Value qualified as Value
import PlutusLedgerApi.Test.Orphans.V2.Tx ()
import PlutusLedgerApi.V1.Credential (StakingCredential)
import PlutusLedgerApi.V1.Crypto (PubKeyHash)
import PlutusLedgerApi.V1.DCert (DCert)
import PlutusLedgerApi.V1.Scripts (Datum, DatumHash, Redeemer)
import PlutusLedgerApi.V1.Time (POSIXTimeRange)
import PlutusLedgerApi.V1.Tx (TxId)
import PlutusLedgerApi.V1.Value (Value)
import PlutusLedgerApi.V2.Contexts (ScriptPurpose, TxInInfo (TxInInfo), TxInfo (TxInfo))
import PlutusLedgerApi.V2.Tx (TxOut)
import PlutusTx.AssocMap (Map)
import Test.QuickCheck (Arbitrary (arbitrary, shrink), CoArbitrary (coarbitrary),
                        Function (function), NonEmptyList (NonEmpty), functionMap, getNonEmpty)

instance Arbitrary TxInInfo where
  {-# INLINEABLE arbitrary #-}
  arbitrary = TxInInfo <$> arbitrary <*> arbitrary

  {-# INLINEABLE shrink #-}
  shrink (TxInInfo outref resolved) =
    TxInInfo <$> shrink outref <*> shrink resolved

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
      <*> arbitrary -- reference inputs
      <*> (getNonEmpty <$> arbitrary) -- outputs
      <*> (Value.getFeeValue <$> arbitrary) -- fee
      <*> (Value.getMintValue <$> arbitrary) -- mint
      <*> arbitrary -- dcert
      <*> arbitrary -- withdrawals
      <*> arbitrary -- valid range
      <*> (Set.toList <$> arbitrary) -- signatures
      <*> arbitrary -- redeemers
      <*> arbitrary -- datums
      <*> arbitrary -- tid

  {-# INLINEABLE shrink #-}
  shrink (TxInfo ins routs outs fee mint dcert wdrl validRange sigs reds dats tid) = do
    NonEmpty ins' <- shrink (NonEmpty ins)
    routs' <- shrink routs
    NonEmpty outs' <- shrink (NonEmpty outs)
    Value.FeeValue fee' <- shrink (Value.FeeValue fee)
    Value.ZeroAdaValue mint' <- shrink (Value.ZeroAdaValue mint)
    dcert' <- shrink dcert
    wdrl' <- shrink wdrl
    validRange' <- shrink validRange
    sigs' <- Set.toList <$> shrink (Set.fromList sigs)
    reds' <- shrink reds
    dats' <- shrink dats
    tid' <- shrink tid
    pure . TxInfo ins' routs' outs' fee' mint' dcert' wdrl' validRange' sigs' reds' dats' $ tid'

instance CoArbitrary TxInfo where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (TxInfo ins routs outs fee mint dcert wdrl validRange sigs reds dats tid) =
    coarbitrary ins
      . coarbitrary routs
      . coarbitrary outs
      . coarbitrary fee
      . coarbitrary mint
      . coarbitrary dcert
      . coarbitrary wdrl
      . coarbitrary validRange
      . coarbitrary sigs
      . coarbitrary reds
      . coarbitrary dats
      . coarbitrary tid

instance Function TxInfo where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        TxInfo ->
        ([TxInInfo]
        , [TxInInfo]
        , [TxOut]
        , Value
        , Value
        , ([DCert]
          , Map StakingCredential Integer
          , POSIXTimeRange
          , [PubKeyHash]
          , Map ScriptPurpose Redeemer
          , Map DatumHash Datum
          , TxId
          )
        )
      into (TxInfo ins routs outs fee mint dcert wdrl validRange sigs reds dats tid) =
        (ins, routs, outs, fee, mint, (dcert, wdrl, validRange, sigs, reds, dats, tid))

      outOf ::
        ([TxInInfo]
        , [TxInInfo]
        , [TxOut]
        , Value
        , Value
        , ([DCert]
          , Map StakingCredential Integer
          , POSIXTimeRange
          , [PubKeyHash]
          , Map ScriptPurpose Redeemer
          , Map DatumHash Datum
          , TxId
          )
        ) ->
        TxInfo
      outOf (ins, routs, outs, fee, mint, (dcert, wdrl, validRange, sigs, reds, dats, tid)) =
        TxInfo ins routs outs fee mint dcert wdrl validRange sigs reds dats tid
