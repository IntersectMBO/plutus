{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.POF.Payoff where

import Data.Time
import Language.Marlowe.ACTUS.ContractState
import Language.Marlowe.ACTUS.BusinessEvents
import Language.Marlowe.ACTUS.POF.PayoffSpec
import Language.Marlowe.ACTUS.ContractTerms

payoff :: ScheduledEvent -> ContractTerms -> ContractState -> Day -> ContractTermsContext -> ContractStateContext -> Double
payoff ev terms ContractState{..} t termsCtx stateCtx = case terms of
    PamContractTerms{..} -> case ev of 
        AD_EVENT{..}   -> _POF_AD_PAM
        IED_EVENT{..}  -> _POF_IED_PAM o_rf_CURS _CNTRL _NT _PDIED
        MD_EVENT{..}   -> _POF_MD_PAM o_rf_CURS nsc nt isc ipac feac
        PP_EVENT{..}   -> _POF_PP_PAM o_rf_CURS pp_payoff
        PY_EVENT{..}   -> _POF_PY_PAM _PYTP o_rf_CURS o_rf_RRMO _PYRT _cPYRT _CNTRL nt _DCC sd t _MD ipnr
        FP_EVENT{..}   -> _POF_FP_PAM _FEB _FER o_rf_CURS _CNTRL _DCC sd t _MD nt fac
        PRD_EVENT{..}  -> _POF_PRD_PAM o_rf_CURS _CNTRL _PPRD ipac _DCC sd t _MD ipnr nt
        TD_EVENT{..}   -> _POF_TD_PAM o_rf_CURS _CNTRL _PTD ipac _DCC sd t _MD ipnr nt 
        IP_EVENT{..}   -> _POF_IP_PAM o_rf_CURS isc ipac _DCC sd t _MD ipnr nt 
        IPCI_EVENT{..} -> _POF_IPCI_PAM 
        RR_EVENT{..}   -> _POF_RR_PAM
        RRF_EVENT{..}  -> _POF_RRF_PAM
        SC_EVENT{..}   -> _POF_SC_PAM
        CE_EVENT{..}   -> _POF_CE_PAM


