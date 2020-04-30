{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.HP.STF.StateTransition where

import Data.Time
import Language.Marlowe.ACTUS.HP.ContractState
import Language.Marlowe.ACTUS.HP.BusinessEvents
import Language.Marlowe.ACTUS.HP.STF.StateTransitionSpec
import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.Utility.ScheduleGenerator
import Language.Marlowe.ACTUS.HP.Schedule
import Language.Marlowe.ACTUS.HP.SCHED.ContractSchedule
import Data.Maybe

stateTransition :: ScheduledEvent -> ContractTerms -> ContractState -> Day -> ContractTermsContext -> ContractStateContext -> ContractState
stateTransition ev terms st@ContractState{..} t termsCtx stateCtx = 
    case terms of
        PamContractTerms{..} -> 
            let 
                fpSchedule = fromJust $ schedule FP terms
                t0 = _SD
                tfp_minus = calculationDay $ sup fpSchedule t0
                tfp_plus = calculationDay $ inf fpSchedule t0
            in case ev of 
                AD_EVENT{..}   -> _STF_AD_PAM st t _DCC _MD
                IED_EVENT{..}  -> _STF_IED_PAM st t _DCC _MD _IPNR _IPANX _CNTRL _IPAC _NT
                MD_EVENT{..}   -> _STF_MD_PAM st t
                PP_EVENT{..}   -> _STF_PP_PAM st t pp_payoff _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL
                PY_EVENT{..}   -> _STF_PY_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL
                FP_EVENT{..}   -> _STF_FP_PAM st t _DCC _MD
                PRD_EVENT{..}  -> _STF_PRD_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL 
                TD_EVENT{..}   -> _STF_IP_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL 
                IP_EVENT{..}   -> _STF_IPCI_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL
                IPCI_EVENT{..} -> _STF_IPCI_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL
                RR_EVENT{..}   -> _STF_RR_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL _RRLF _RRLC _RRPC _RRPF _RRMLT _RRSP o_rf_RRMO
                RRF_EVENT{..}  -> _STF_RRF_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL _RRNXT 
                SC_EVENT{..}   -> _STF_SC_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL _SCEF o_rf_SCMO _SCIED
                CE_EVENT{..}   -> _STF_CE_PAM st t _DCC _MD


     

    
     
    
     
    