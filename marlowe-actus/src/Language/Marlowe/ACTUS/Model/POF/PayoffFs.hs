{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.POF.PayoffFs where

import           Data.Time                                         (LocalTime)
import           Language.Marlowe                                  (Observation, Value)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents (EventType (..), RiskFactorsPoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms  (CT (..), ContractTerms (..))
import           Language.Marlowe.ACTUS.MarloweCompat              (RiskFactorsMarlowe, constnt, enum, useval)
import           Language.Marlowe.ACTUS.Model.POF.PayoffModel
import           Language.Marlowe.ACTUS.Ops                        (ActusNum (..), YearFractionOps (_y),
                                                                    marloweFixedPoint)
import           Prelude                                           hiding (Fractional, Num, (*), (+), (-), (/))

payoffFs :: EventType -> RiskFactorsMarlowe -> ContractTerms -> Integer -> LocalTime -> LocalTime -> Maybe (Value Observation)
payoffFs
  ev
  RiskFactorsPoly {..}
  ContractTerms
    { ct_NT = Just np,
      ct_PDIED = Just pdied,
      ct_PYTP = Just pytp,
      ct_FEB = Just feb,
      ct_FER = Just fer,
      ct_PPRD = Just pprd,
      ct_PYRT = Just pyrt,
      ct_PTD = Just ptd,
      ct_DCC = Just dayCountConvention,
      ..
    }
  t_minus
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
      premiumDiscount = constnt pdied
      penaltyType = enum pytp
      feeBase = enum feb
      feeRate = constnt fer
      priceAtPurchaseDate = constnt pprd
      priceAtTerminationDate = constnt ptd
      penaltyRate = constnt pyrt
      nsc = useval "nsc" t_minus
      nt = useval "nt" t_minus
      isc = useval "isc" t_minus
      ipac = useval "ipac" t_minus
      feac = useval "feac" t_minus
      ipnr = useval "ipnr" t_minus
      ipcb = useval "ipcb" t_minus
      prnxt = useval "prnxt" t_minus
      y_sd_t = constnt $ _y dayCountConvention prevDate curDate ct_MD
payoffFs _ _ _ _ _ _ = Nothing
