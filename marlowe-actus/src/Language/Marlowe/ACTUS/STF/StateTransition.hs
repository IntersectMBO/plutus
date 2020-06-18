{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.STF.StateTransition where

import Data.Time ( Day )
import Language.Marlowe.ACTUS.ContractState
    ( ContractStatePoly(ContractStatePoly, ipcb, prnxt, sd, prf, isc,
                        nsc, fac, feac, ipac, ipnr, nt, tmd),
      ContractState )
import Language.Marlowe.ACTUS.BusinessEvents
    ( ScheduledEvent(CE_EVENT, AD_EVENT, IED_EVENT, MD_EVENT, PP_EVENT,
                     PY_EVENT, FP_EVENT, PRD_EVENT, TD_EVENT, IP_EVENT, IPCI_EVENT,
                     RR_EVENT, RRF_EVENT, SC_EVENT, pp_payoff, o_rf_RRMO, o_rf_SCMO,
                     o_rf_CURS, creditDate),
      EventType(FP) )
import Language.Marlowe.ACTUS.STF.StateTransitionModel
    ( _STF_AD_PAM,
      _STF_IED_PAM,
      _STF_MD_PAM,
      _STF_PP_PAM,
      _STF_PY_PAM,
      _STF_FP_PAM,
      _STF_PRD_PAM,
      _STF_IP_PAM,
      _STF_IPCI_PAM,
      _STF_RR_PAM,
      _STF_RRF_PAM,
      _STF_SC_PAM,
      _STF_CE_PAM )
import Language.Marlowe.ACTUS.ContractTerms
    ( ContractTerms(..), ContractType(LAM, PAM), ScheduleConfig )
import Language.Marlowe.ACTUS.Utility.ScheduleGenerator
    ( sup, inf )
import Language.Marlowe.ACTUS.Schedule
    ( ShiftedDay(calculationDay) )
import Language.Marlowe.ACTUS.SCHED.ContractSchedule ( schedule )
import Language.Marlowe.ACTUS.Ops ( YearFractionOps(_y) )
import Data.Maybe ( fromJust, fromMaybe )


import Language.Marlowe.ACTUS.Utility.DateShift

shift :: ScheduleConfig -> Day -> ShiftedDay
shift = applyBDCWithCfg

stateTransition :: ScheduledEvent -> ContractTerms -> ContractState -> Day -> ContractState
stateTransition ev terms@ContractTerms{..} st@ContractStatePoly{..} t = 
    let 
        fpSchedule         = fromMaybe [shift scfg _SD] $ schedule FP terms
        tfp_minus          = calculationDay $ sup fpSchedule t
        tfp_plus           = calculationDay $ inf fpSchedule t
        y_sd_t             = _y _DCC sd t _MD
        y_tfpminus_t       = _y _DCC tfp_minus t _MD
        y_tfpminus_tfpplus = _y _DCC tfp_minus tfp_plus _MD
        y_ipanx_t          = _y _DCC (fromJust _IPANX) t _MD
    in case contractType of
        PAM -> 
            case ev of 
                AD_EVENT{..}   -> _STF_AD_PAM st t y_sd_t
                IED_EVENT{..}  -> _STF_IED_PAM st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
                MD_EVENT{..}   -> _STF_MD_PAM st t
                PP_EVENT{..}   -> _STF_PP_PAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
                PY_EVENT{..}   -> _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
                FP_EVENT{..}   -> _STF_FP_PAM st t y_sd_t
                PRD_EVENT{..}  -> _STF_PRD_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL 
                TD_EVENT{..}   -> _STF_IP_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL 
                IP_EVENT{..}   -> _STF_IPCI_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
                IPCI_EVENT{..} -> _STF_IPCI_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
                RR_EVENT{..}   -> _STF_RR_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRLF _RRLC _RRPC _RRPF _RRMLT _RRSP o_rf_RRMO
                RRF_EVENT{..}  -> _STF_RRF_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRNXT 
                SC_EVENT{..}   -> _STF_SC_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _SCEF o_rf_SCMO _SCIED
                CE_EVENT{..}   -> _STF_CE_PAM st t y_sd_t
                _             -> st
        LAM -> undefined


     

    
     
    
     
    