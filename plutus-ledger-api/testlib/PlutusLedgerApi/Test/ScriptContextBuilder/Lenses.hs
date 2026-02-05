{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ImplicitPrelude #-}

module PlutusLedgerApi.Test.ScriptContextBuilder.Lenses
  ( scriptContextTxInfoL
  , scriptContextRedeemerL
  , scriptContextScriptInfoL
  , txInfoInputsL
  , txInfoMintL
  , txInfoSignatoriesL
  , txInfoOutputsL
  , txInfoValidRangeL
  , txInfoRedeemersL
  , txInfoFeeL
  , txInfoWdrlL
  , txInfoVotesL
  , txInfoTxCertsL
  , txInfoTreasuryDonationL
  , txInfoReferenceInputsL
  , txInfoProposalProceduresL
  , txInfoIdL
  , txInfoDataL
  , txInfoCurrentTreasuryAmountL
  , txInInfoOutRefL
  , txInInfoResolvedL
  , txOutRefIdL
  , txOutRefIdxL
  , txOutAddressL
  , txOutValueL
  , txOutDatumL
  , txOutReferenceScriptL
  , addressCredentialL
  , addressStakingCredentialL
  , mintValueMapL
  , valueMapL
  , ivFromL
  , ivToL
  , lowerBoundExtendedL
  , lowerBoundClosureL
  , upperBoundExtendedL
  , upperBoundClosureL
  , _NegInf
  , _Finite
  , _PosInf
  , _NoOutputDatum
  , _OutputDatumHash
  , _OutputDatum
  , _Datum
  , _Redeemer
  )
where

import Control.Lens qualified as L
import Data.List (sortBy)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Ord (comparing)
import PlutusLedgerApi.Test.ScriptContextBuilder.Lenses.TH (makeLensesWithL)
import PlutusLedgerApi.V1 qualified as PV1
import PlutusLedgerApi.V3
  ( OutputDatum
  , ScriptContext
  , TxInInfo
  , TxInfo
  , TxOut
  , TxOutRef
  )
import PlutusLedgerApi.V3 qualified as PV3
import PlutusLedgerApi.V3.MintValue
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Prelude qualified as PlutusTx

makeLensesWithL ''ScriptContext

L.makeLensesFor
  [ ("txInfoInputs", "txInfoInputsL")
  , ("txInfoMint", "txInfoMintL")
  , ("txInfoSignatories", "txInfoSignatoriesL")
  , ("txInfoOutputs", "txInfoOutputsL")
  , ("txInfoValidRange", "txInfoValidRangeL")
  , ("txInfoFee", "txInfoFeeL")
  , ("txInfoWdrl", "txInfoWdrlL")
  , ("txInfoVotes", "txInfoVotesL")
  , ("txInfoTxCerts", "txInfoTxCertsL")
  , ("txInfoTreasuryDonation", "txInfoTreasuryDonationL")
  , ("txInfoReferenceInputs", "txInfoReferenceInputsL")
  , ("txInfoProposalProcedures", "txInfoProposalProceduresL")
  , ("txInfoId", "txInfoIdL")
  , ("txInfoData", "txInfoDataL")
  , ("txInfoCurrentTreasuryAmount", "txInfoCurrentTreasuryAmountL")
  ]
  ''TxInfo

makeLensesWithL ''TxInInfo

makeLensesWithL ''TxOutRef

makeLensesWithL ''TxOut

makeLensesWithL ''PV1.Address

L.makePrisms ''PV1.Credential
L.makePrisms ''PV1.StakingCredential
L.makePrisms ''OutputDatum

makeLensesWithL ''PV1.Interval

L.makePrisms ''PV1.Extended

_Datum :: forall a. (PV1.FromData a, PV1.ToData a) => L.Prism' PV1.Datum a
_Datum = L.prism' from to
  where
    to :: PV1.Datum -> Maybe a
    to = PV1.fromBuiltinData . PV1.getDatum

    from :: a -> PV1.Datum
    from = PV1.Datum . PV1.toBuiltinData

_Redeemer :: forall a. (PV1.FromData a, PV1.ToData a) => L.Prism' PV1.Redeemer a
_Redeemer = L.prism' from to
  where
    to :: PV1.Redeemer -> Maybe a
    to = PV1.fromBuiltinData . PV1.getRedeemer

    from :: a -> PV1.Redeemer
    from = PV1.Redeemer . PV1.toBuiltinData

txInfoRedeemersL :: L.Lens' PV3.TxInfo (Map PV3.ScriptPurpose PV3.Redeemer)
txInfoRedeemersL = L.lens getter setter
  where
    getter txInfo = Map.fromList $ AssocMap.toList $ PV3.txInfoRedeemers txInfo
    setter txInfo redeemerMap = txInfo {PV3.txInfoRedeemers = AssocMap.unsafeFromList $ Map.toList redeemerMap}

mintValueMapL :: L.Lens' MintValue (Map PV1.CurrencySymbol (Map PV1.TokenName Integer))
mintValueMapL = L.lens getter setter
  where
    getter mp = Map.fromList $ AssocMap.toList $ PlutusTx.fmap (\v -> Map.fromList $ AssocMap.toList v) $ mintValueToMap mp
    setter _ v =
      UnsafeMintValue $
        AssocMap.unsafeFromList $
          sortBy (comparing fst) $
            Map.toList $
              fmap (AssocMap.unsafeFromList . sortBy (comparing fst) . Map.toList) v

valueMapL :: L.Lens' PV1.Value (Map PV1.CurrencySymbol (Map PV1.TokenName Integer))
valueMapL = L.lens getter setter
  where
    getter mp =
      Map.fromList $
        AssocMap.toList $
          PlutusTx.fmap (\v -> Map.fromList $ AssocMap.toList v) $
            PV1.getValue mp
    setter _ v =
      PV1.Value $
        AssocMap.unsafeFromList $
          sortBy (comparing fst) $
            Map.toList $
              fmap (AssocMap.unsafeFromList . sortBy (comparing fst) . Map.toList) v

lowerBoundExtendedL :: L.Lens' (PV1.LowerBound a) (PV1.Extended a)
lowerBoundExtendedL = L.lens getter setter
  where
    getter (PV1.LowerBound e _) = e
    setter (PV1.LowerBound _ c) e = PV1.LowerBound e c

lowerBoundClosureL :: L.Lens' (PV1.LowerBound a) PV1.Closure
lowerBoundClosureL = L.lens getter setter
  where
    getter (PV1.LowerBound _ c) = c
    setter (PV1.LowerBound e _) c = PV1.LowerBound e c

upperBoundExtendedL :: L.Lens' (PV1.UpperBound a) (PV1.Extended a)
upperBoundExtendedL = L.lens getter setter
  where
    getter (PV1.UpperBound e _) = e
    setter (PV1.UpperBound _ c) e = PV1.UpperBound e c

upperBoundClosureL :: L.Lens' (PV1.UpperBound a) PV1.Closure
upperBoundClosureL = L.lens getter setter
  where
    getter (PV1.UpperBound _ c) = c
    setter (PV1.UpperBound e _) c = PV1.UpperBound e c
