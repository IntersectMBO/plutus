{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.STF.StateTransition where

import Data.Time
import Language.Marlowe.ACTUS.ContractState
import Language.Marlowe.ACTUS.BusinessEvents
import Language.Marlowe.ACTUS.STF.StateTransitionSpec
import Language.Marlowe.ACTUS.ContractTerms
import Language.Marlowe.ACTUS.Utility.ScheduleGenerator
import Language.Marlowe.ACTUS.Schedule
import Language.Marlowe.ACTUS.SCHED.ContractSchedule
import Language.Marlowe.ACTUS.Ops
import Data.Maybe

import Language.Marlowe.ACTUS.Utility.DateShift

shift = applyBDCWithCfg

stateTransition :: ScheduledEvent -> ContractTerms -> ContractState -> Day -> ContractTermsContext -> ContractStateContext -> ContractState
stateTransition ev terms st@ContractStatePoly{..} t termsCtx stateCtx = 
    case terms of
        PamContractTerms{..} -> 
            let 
                t0 = _SD
                fpSchedule = fromMaybe [shift scfg t0] $ schedule FP terms
                tfp_minus = calculationDay $ sup fpSchedule t0
                tfp_plus = calculationDay $ inf fpSchedule t0
                y_sd_t = _y _DCC sd t _MD
                y_tfpminus_t = _y _DCC tfp_minus t _MD
                y_tfpminus_tfpplus = _y _DCC tfp_minus tfp_plus _MD
                y_ipanx_t = _y _DCC (fromJust _IPANX) t _MD
                r_CNTRL = _r _CNTRL
                ipanx_lt_t = if (fromJust _IPANX) < t then _one else _zero
            in case ev of 
                AD_EVENT{..}   -> _STF_AD_PAM st t y_sd_t
                IED_EVENT{..}  -> _STF_IED_PAM st t y_ipanx_t ipanx_lt_t y_sd_t _IPNR _IPANX r_CNTRL _IPAC _NT
                MD_EVENT{..}   -> _STF_MD_PAM st t
                PP_EVENT{..}   -> _STF_PP_PAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL
                PY_EVENT{..}   -> _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL
                FP_EVENT{..}   -> _STF_FP_PAM st t y_sd_t
                PRD_EVENT{..}  -> _STF_PRD_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL 
                TD_EVENT{..}   -> _STF_IP_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL 
                IP_EVENT{..}   -> _STF_IPCI_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL
                IPCI_EVENT{..} -> _STF_IPCI_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL
                RR_EVENT{..}   -> _STF_RR_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL _RRLF _RRLC _RRPC _RRPF _RRMLT _RRSP o_rf_RRMO
                RRF_EVENT{..}  -> _STF_RRF_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL _RRNXT 
                SC_EVENT{..}   -> _STF_SC_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL _SCEF o_rf_SCMO _SCIED
                CE_EVENT{..}   -> _STF_CE_PAM st t y_sd_t


     

    
     
    
     
    