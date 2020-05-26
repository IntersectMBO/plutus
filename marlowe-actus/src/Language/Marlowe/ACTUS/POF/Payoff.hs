{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.POF.Payoff where

import           Data.Time
import           Language.Marlowe.ACTUS.ContractState
import           Language.Marlowe.ACTUS.BusinessEvents
import           Language.Marlowe.ACTUS.POF.PayoffSpec
import           Language.Marlowe.ACTUS.ContractTerms
import           Language.Marlowe.ACTUS.Ops


payoff :: ScheduledEvent -> ContractTerms -> ContractState -> Day -> Double
payoff ev terms ContractStatePoly {..} t = case terms of
    PamContractTerms {..} ->
        let
            y_sd_t  = _y _DCC sd t _MD
        in
            case ev of
                IED_EVENT {..} -> _POF_IED_PAM o_rf_CURS _CNTRL _NT _PDIED
                MD_EVENT {..}  -> _POF_MD_PAM o_rf_CURS nsc nt isc ipac feac
                PP_EVENT {..}  -> _POF_PP_PAM o_rf_CURS pp_payoff
                PY_EVENT {..}  -> _POF_PY_PAM _PYTP o_rf_CURS o_rf_RRMO _PYRT _cPYRT _CNTRL nt ipnr y_sd_t
                FP_EVENT {..}  -> _POF_FP_PAM _FEB _FER o_rf_CURS _CNTRL nt fac y_sd_t
                PRD_EVENT {..} -> _POF_PRD_PAM o_rf_CURS _CNTRL _PPRD ipac ipnr nt y_sd_t
                TD_EVENT {..}  -> _POF_TD_PAM o_rf_CURS _CNTRL _PTD ipac ipnr nt y_sd_t
                IP_EVENT {..}  -> _POF_IP_PAM o_rf_CURS isc ipac ipnr nt y_sd_t
                _             -> 0.0
    LamContractTerms {..} -> undefined


