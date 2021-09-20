{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.POF.PayoffFs where

import           Data.Maybe                                        (fromMaybe)
import           Data.Time                                         (LocalTime)
import           Language.Marlowe                                  (Observation, Value)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents (EventType (..), RiskFactorsMarlowe,
                                                                    RiskFactorsPoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState  (ContractStateMarlowe, ContractStatePoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms  (CT (..), ContractTerms, ContractTermsPoly (..),
                                                                    FEB (..))
import           Language.Marlowe.ACTUS.MarloweCompat              (constnt, enum)
import           Language.Marlowe.ACTUS.Model.POF.PayoffModel
import           Language.Marlowe.ACTUS.Ops                        (ActusNum (..), YearFractionOps (_y),
                                                                    marloweFixedPoint)
import           Prelude                                           hiding (Fractional, Num, (*), (+), (-), (/))

payoffFs :: EventType -> RiskFactorsMarlowe -> ContractTerms -> ContractStateMarlowe -> LocalTime -> LocalTime -> Maybe (Value Observation)
payoffFs
  ev
  RiskFactorsPoly {..}
  ContractTermsPoly
    { ct_NT = Just np,
      ct_PYTP = Just pytp,
      ct_DCC = Just dayCountConvention,
      ..
    }
  ContractStatePoly {..}
  prevDate
  curDate =
    let pof = case contractType of
          PAM -> case ev of
            IED -> Just $ _POF_IED_PAM o_rf_CURS ct_CNTRL notionalPrincipal premiumDiscount
            MD  -> Just $ _POF_MD_PAM o_rf_CURS nsc nt isc ipac feac
            PP  -> Just $ _POF_PP_PAM o_rf_CURS pp_payoff
            PY  -> Just $ _POF_PY_PAM penaltyType o_rf_CURS o_rf_RRMO penaltyRate ct_CNTRL nt ipnr y_sd_t
            FP  -> Just $ _POF_FP_PAM feeBase feeRate o_rf_CURS ct_CNTRL nt feac y_sd_t
            PRD -> Just $ _POF_PRD_PAM o_rf_CURS ct_CNTRL priceAtPurchaseDate ipac ipnr nt y_sd_t
            TD  -> Just $ _POF_TD_PAM o_rf_CURS ct_CNTRL priceAtTerminationDate ipac ipnr nt y_sd_t
            IP  -> Just $ _POF_IP_PAM o_rf_CURS isc ipac ipnr nt y_sd_t
            _   -> Nothing
          LAM -> case ev of
            IED -> Just $ _POF_IED_PAM o_rf_CURS ct_CNTRL notionalPrincipal premiumDiscount
            PR  -> Just $ _POF_PR_LAM o_rf_CURS ct_CNTRL nt nsc prnxt
            MD  -> Just $ _POF_MD_PAM o_rf_CURS nsc nt isc ipac feac
            PP  -> Just $ _POF_PP_PAM o_rf_CURS pp_payoff
            PY  -> Just $ _POF_PY_PAM penaltyType o_rf_CURS o_rf_RRMO penaltyRate ct_CNTRL nt ipnr y_sd_t
            FP  -> Just $ _POF_FP_PAM feeBase feeRate o_rf_CURS ct_CNTRL nt feac y_sd_t
            PRD -> Just $ _POF_PRD_LAM o_rf_CURS ct_CNTRL priceAtPurchaseDate ipac ipnr ipcb y_sd_t
            TD  -> Just $ _POF_TD_LAM o_rf_CURS ct_CNTRL priceAtTerminationDate ipac ipnr ipcb y_sd_t
            IP  -> Just $ _POF_IP_LAM o_rf_CURS isc ipac ipnr ipcb y_sd_t
            _   -> Nothing
          NAM -> case ev of
            IED -> Just $ _POF_IED_PAM o_rf_CURS ct_CNTRL notionalPrincipal premiumDiscount
            PR  -> Just $ _POF_PR_NAM o_rf_CURS ct_CNTRL nsc prnxt ipac y_sd_t ipnr ipcb nt
            MD  -> Just $ _POF_MD_PAM o_rf_CURS nsc nt isc ipac feac
            PP  -> Just $ _POF_PP_PAM o_rf_CURS pp_payoff
            PY  -> Just $ _POF_PY_PAM penaltyType o_rf_CURS o_rf_RRMO penaltyRate ct_CNTRL nt ipnr y_sd_t
            FP  -> Just $ _POF_FP_PAM feeBase feeRate o_rf_CURS ct_CNTRL nt feac y_sd_t
            PRD -> Just $ _POF_PRD_LAM o_rf_CURS ct_CNTRL priceAtPurchaseDate ipac ipnr ipcb y_sd_t
            TD  -> Just $ _POF_TD_LAM o_rf_CURS ct_CNTRL priceAtTerminationDate ipac ipnr ipcb y_sd_t
            IP  -> Just $ _POF_IP_LAM o_rf_CURS isc ipac ipnr ipcb y_sd_t
            _   -> Nothing
          ANN -> case ev of
            IED -> Just $ _POF_IED_PAM o_rf_CURS ct_CNTRL notionalPrincipal premiumDiscount
            PR  -> Just $ _POF_PR_NAM o_rf_CURS ct_CNTRL nsc prnxt ipac y_sd_t ipnr ipcb nt
            MD  -> Just $ _POF_MD_PAM o_rf_CURS nsc nt isc ipac feac
            PP  -> Just $ _POF_PP_PAM o_rf_CURS pp_payoff
            PY  -> Just $ _POF_PY_PAM penaltyType o_rf_CURS o_rf_RRMO penaltyRate ct_CNTRL nt ipnr y_sd_t
            FP  -> Just $ _POF_FP_PAM feeBase feeRate o_rf_CURS ct_CNTRL nt feac y_sd_t
            PRD -> Just $ _POF_PRD_LAM o_rf_CURS ct_CNTRL priceAtPurchaseDate ipac ipnr ipcb y_sd_t
            TD  -> Just $ _POF_TD_LAM o_rf_CURS ct_CNTRL priceAtTerminationDate ipac ipnr ipcb y_sd_t
            IP  -> Just $ _POF_IP_LAM o_rf_CURS isc ipac ipnr ipcb y_sd_t
            _   -> Nothing
     in (\x -> x / (constnt $ fromIntegral marloweFixedPoint)) <$> pof
    where
      notionalPrincipal = constnt np
      premiumDiscount = constnt (fromMaybe 0.0 ct_PDIED)
      penaltyType = enum pytp
      feeBase = enum (fromMaybe FEB_N ct_FEB)
      feeRate = constnt (fromMaybe 0.0 ct_FER)
      priceAtPurchaseDate = constnt (fromMaybe 0.0 ct_PPRD)
      priceAtTerminationDate = constnt (fromMaybe 0.0 ct_PTD)
      penaltyRate = constnt (fromMaybe 0.0 ct_PYRT)
      y_sd_t = constnt $ _y dayCountConvention prevDate curDate ct_MD
payoffFs _ _ _ _ _ _ = Nothing
