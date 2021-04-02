{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.POF.Payoff where

import           Data.Maybe                                        (fromJust)
import           Data.Time                                         (Day)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents (EventType (..), RiskFactors (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState  (ContractState, ContractStatePoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms  (ContractTerms (..), ContractType (LAM, NAM, PAM))
import           Language.Marlowe.ACTUS.Model.POF.PayoffModel
import           Language.Marlowe.ACTUS.Ops                        (YearFractionOps (_y))



payoff :: EventType -> RiskFactors -> ContractTerms -> ContractState -> Day -> Double
payoff ev RiskFactors{..} ContractTerms{..} ContractStatePoly {..} t =
    let
        y_sd_t = _y ct_DCC sd t (fromJust ct_MD)
    in case fromJust contractType of
        PAM ->
            case ev of
                IED -> _POF_IED_PAM o_rf_CURS ct_CNTRL (fromJust ct_NT) ct_PDIED
                MD  -> _POF_MD_PAM o_rf_CURS nsc nt isc ipac feac
                PP  -> _POF_PP_PAM o_rf_CURS pp_payoff
                PY  -> _POF_PY_PAM ct_PYTP o_rf_CURS o_rf_RRMO ct_PYRT ct_cPYRT ct_CNTRL nt ipnr y_sd_t
                FP  -> _POF_FP_PAM ct_FEB ct_FER o_rf_CURS ct_CNTRL nt fac y_sd_t
                PRD -> _POF_PRD_PAM o_rf_CURS ct_CNTRL (fromJust ct_PPRD) ipac ipnr nt y_sd_t
                TD  -> _POF_TD_PAM o_rf_CURS ct_CNTRL (fromJust ct_PTD) ipac ipnr nt y_sd_t
                IP  -> _POF_IP_PAM o_rf_CURS isc ipac ipnr nt y_sd_t
                _   -> 0.0
        LAM ->
            case ev of
                IED -> _POF_IED_LAM o_rf_CURS ct_CNTRL (fromJust ct_NT) ct_PDIED
                PR  -> _POF_PR_LAM o_rf_CURS ct_CNTRL nsc prnxt
                MD  -> _POF_MD_LAM o_rf_CURS nsc nt isc ipac feac
                PP  -> _POF_PP_LAM o_rf_CURS pp_payoff
                PY  -> _POF_PY_LAM ct_PYTP o_rf_CURS o_rf_RRMO ct_PYRT ct_cPYRT ct_CNTRL nt ipnr y_sd_t
                FP  -> _POF_FP_LAM ct_FEB ct_FER o_rf_CURS ct_CNTRL nt fac y_sd_t
                PRD -> _POF_PRD_LAM o_rf_CURS ct_CNTRL (fromJust ct_PPRD) ipac ipnr ipcb y_sd_t
                TD  -> _POF_TD_LAM o_rf_CURS ct_CNTRL (fromJust ct_PTD) ipac ipnr ipcb y_sd_t
                IP  -> _POF_IP_LAM o_rf_CURS isc ipac ipnr ipcb y_sd_t
                _   -> 0.0
        NAM ->
            case ev of
                IED -> _POF_IED_NAM o_rf_CURS ct_CNTRL (fromJust ct_NT) ct_PDIED
                PR  -> _POF_PR_NAM o_rf_CURS nsc prnxt ipac y_sd_t ipnr ipcb
                MD  -> _POF_MD_NAM o_rf_CURS nsc nt isc ipac feac
                PP  -> _POF_PP_NAM o_rf_CURS pp_payoff
                PY  -> _POF_PY_NAM ct_PYTP o_rf_CURS o_rf_RRMO ct_PYRT ct_cPYRT ct_CNTRL nt ipnr y_sd_t
                FP  -> _POF_FP_NAM ct_FEB ct_FER o_rf_CURS ct_CNTRL nt fac y_sd_t
                PRD -> _POF_PRD_NAM o_rf_CURS ct_CNTRL (fromJust ct_PPRD) ipac ipnr ipcb y_sd_t
                TD  -> _POF_TD_NAM o_rf_CURS ct_CNTRL (fromJust ct_PTD) ipac ipnr ipcb y_sd_t
                IP  -> _POF_IP_NAM o_rf_CURS isc ipac ipnr ipcb y_sd_t
                _   -> 0.0
