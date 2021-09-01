{-# LANGUAGE BlockArguments           #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE NamedFieldPuns           #-}
{-# LANGUAGE TypeApplications         #-}
-- Code temporarily copied over from cardano-api,
-- until https://github.com/input-output-hk/cardano-node/pull/2936 or something similar gets merged.
module Plutus.Contract.CardanoAPITemp (makeTransactionBody') where

import qualified Data.Map.Strict                    as Map
import qualified Data.Sequence.Strict               as Seq
import qualified Data.Set                           as Set

import           Cardano.Api
import           Cardano.Api.Shelley                hiding (toShelleyTxOut)
import           Cardano.Ledger.BaseTypes           (StrictMaybe (..))
import           Cardano.Ledger.Crypto              (StandardCrypto)
import           Ouroboros.Consensus.Shelley.Eras   (StandardAlonzo)

import qualified Cardano.Ledger.Core                as Ledger
import qualified Cardano.Ledger.Shelley.Constraints as Ledger

import qualified Cardano.Ledger.Alonzo.Data         as Alonzo
import qualified Cardano.Ledger.Alonzo.Tx           as Alonzo
import qualified Cardano.Ledger.Alonzo.TxBody       as Alonzo
import qualified Cardano.Ledger.Alonzo.TxWitness    as Alonzo

import qualified Cardano.Ledger.ShelleyMA.TxBody    as Allegra

import qualified Cardano.Ledger.Keys                as Shelley
import qualified Shelley.Spec.Ledger.Tx             as Shelley
import qualified Shelley.Spec.Ledger.TxBody         as Shelley

makeTransactionBody' :: TxBodyContent BuildTx AlonzoEra -> Either TxBodyError (TxBody AlonzoEra)
makeTransactionBody'
    txbodycontent@TxBodyContent {
        txIns,
        txInsCollateral,
        txOuts,
        txFee,
        txValidityRange = (lowerBound, upperBound),
        txExtraScriptData,
        txExtraKeyWits,
        txWithdrawals,
        txCertificates,
        txMintValue,
        txScriptValidity
    } =
    return $
      ShelleyTxBody ShelleyBasedEraAlonzo
        (Alonzo.TxBody
          (Set.fromList (map (toShelleyTxIn . fst) txIns))
          (case txInsCollateral of
             TxInsCollateralNone     -> Set.empty
             TxInsCollateral _ txins -> Set.fromList (map toShelleyTxIn txins))
          (Seq.fromList (map toShelleyTxOut txOuts))
          (case txCertificates of
             TxCertificatesNone    -> Seq.empty
             TxCertificates _ cs _ -> Seq.fromList (map toShelleyCertificate cs))
          (case txWithdrawals of
             TxWithdrawalsNone  -> Shelley.Wdrl Map.empty
             TxWithdrawals _ ws -> toShelleyWithdrawal ws)
          (case txFee of
             TxFeeImplicit era'  -> case era' of {}
             TxFeeExplicit _ fee -> toShelleyLovelace fee)
          (Allegra.ValidityInterval {
             invalidBefore    = case lowerBound of
                                          TxValidityNoLowerBound   -> SNothing
                                          TxValidityLowerBound _ s -> SJust s,
             invalidHereafter = case upperBound of
                                          TxValidityNoUpperBound _ -> SNothing
                                          TxValidityUpperBound _ s -> SJust s
           })
          SNothing -- ignoring txUpdatePropsal in CardanoAPITemp
          (case txExtraKeyWits of
             TxExtraKeyWitnessesNone   -> Set.empty
             TxExtraKeyWitnesses _ khs -> Set.fromList
                                            [ Shelley.coerceKeyRole kh
                                            | PaymentKeyHash kh <- khs ])
          (case txMintValue of
             TxMintNone        -> mempty
             TxMintValue _ v _ -> toMaryValue v)
          SNothing -- ignoring txProtocolParams in CardanoAPITemp
          SNothing -- ignoring txMetadata and txAuxScripts in CardanoAPITemp
          SNothing) -- TODO alonzo: support optional network id in TxBodyContent
        scripts
        (TxBodyScriptData ScriptDataInAlonzoEra datums redeemers)
        Nothing -- ignoring txMetadata and txAuxScripts in CardanoAPITemp
        (unBuildTxWith txScriptValidity)
        -- TODO alonzo: support the supplementary script data
  where
    witnesses :: [(ScriptWitnessIndex, AnyScriptWitness AlonzoEra)]
    witnesses = collectTxBodyScriptWitnesses txbodycontent

    scripts :: [Ledger.Script StandardAlonzo]
    scripts =
      [ toShelleyScript (scriptWitnessScript scriptwitness)
      | (_, AnyScriptWitness scriptwitness) <- witnesses
      ]

    datums :: Alonzo.TxDats StandardAlonzo
    datums =
      Alonzo.TxDats $
        Map.fromList
          [ (Alonzo.hashData d', d')
          | d <- scriptdata
          , let d' = toAlonzoData d
          ]

    scriptdata :: [ScriptData]
    scriptdata =
        [ d | BuildTxWith (TxExtraScriptData _ ds) <- [txExtraScriptData], d <- ds ]
     ++ [ d | (_, AnyScriptWitness
                    (PlutusScriptWitness
                       _ _ _ (ScriptDatumForTxIn d) _ _)) <- witnesses
            ]

    redeemers :: Alonzo.Redeemers StandardAlonzo
    redeemers =
      Alonzo.Redeemers $
        Map.fromList
          [ (toAlonzoRdmrPtr idx, (toAlonzoData d, toAlonzoExUnits e))
          | (idx, AnyScriptWitness
                    (PlutusScriptWitness _ _ _ _ d e)) <- witnesses
          ]

unBuildTxWith :: BuildTxWith BuildTx a -> a
unBuildTxWith (BuildTxWith a) = a

toShelleyWithdrawal :: [(StakeAddress, Lovelace, a)] -> Shelley.Wdrl StandardCrypto
toShelleyWithdrawal withdrawals =
    Shelley.Wdrl $
      Map.fromList
        [ (toShelleyStakeAddr stakeAddr, toShelleyLovelace value)
        | (stakeAddr, value, _) <- withdrawals ]

toShelleyTxOut :: forall era ledgerera.
                 (ShelleyLedgerEra era ~ ledgerera,
                  IsShelleyBasedEra era, Ledger.ShelleyBased ledgerera)
               => TxOut era -> Ledger.TxOut ledgerera
toShelleyTxOut (TxOut _ (TxOutAdaOnly AdaOnlyInByronEra _) _) =
    case shelleyBasedEra :: ShelleyBasedEra era of {}

toShelleyTxOut (TxOut addr (TxOutAdaOnly AdaOnlyInShelleyEra value) _) =
    Shelley.TxOut (toShelleyAddr addr) (toShelleyLovelace value)

toShelleyTxOut (TxOut addr (TxOutAdaOnly AdaOnlyInAllegraEra value) _) =
    Shelley.TxOut (toShelleyAddr addr) (toShelleyLovelace value)

toShelleyTxOut (TxOut addr (TxOutValue MultiAssetInMaryEra value) _) =
    Shelley.TxOut (toShelleyAddr addr) (toMaryValue value)

toShelleyTxOut (TxOut addr (TxOutValue MultiAssetInAlonzoEra value) txoutdata) =
    Alonzo.TxOut (toShelleyAddr addr) (toMaryValue value)
                 (toAlonzoTxOutDataHash txoutdata)

toAlonzoTxOutDataHash :: TxOutDatumHash era
                      -> StrictMaybe (Alonzo.DataHash StandardCrypto)
toAlonzoTxOutDataHash TxOutDatumHashNone                     = SNothing
toAlonzoTxOutDataHash (TxOutDatumHash _ (ScriptDataHash dh)) = SJust dh
