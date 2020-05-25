{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.STF.StateTransitionLp (stateTransitionLp) where

import Language.Marlowe
import Language.Marlowe.ACTUS.BusinessEvents
import Language.Marlowe.ACTUS.STF.StateTransitionSpec
import Language.Marlowe.ACTUS.ContractTerms
import Language.Marlowe.ACTUS.Utility.ScheduleGenerator
import Language.Marlowe.ACTUS.Schedule
import Language.Marlowe.ACTUS.SCHED.ContractSchedule
import Language.Marlowe.ACTUS.MarloweCompat
import Language.Marlowe.ACTUS.Ops
import Data.Maybe
import Data.Time

import Language.Marlowe.ACTUS.Utility.DateShift

shift :: ScheduleConfig -> Day -> ShiftedDay
shift = applyBDCWithCfg

stateTransitionLp :: ContractTerms -> Integer -> Contract -> Contract
stateTransitionLp terms t continue = 
    case terms of
        PamContractTerms{..} -> 
            let 
                t0         = _SD
                time       = SlotIntervalStart
                --todo refactor: factor out date to slot, factor _y and _r back in, introduce _lt _gt type-class
                fpSchedule = fromMaybe [shift scfg t0] $ schedule FP terms
                tfp_minus  = constnt $ fromInteger $ dayToSlotNumber $ calculationDay $ sup fpSchedule t0
                tfp_plus   = constnt $ fromInteger $ dayToSlotNumber $ calculationDay $ inf fpSchedule t0
                ipanx      = constnt $ fromInteger $ dayToSlotNumber $ fromJust _IPANX

                y_sd_t             = _y _DCC (useval "sd" t) time undefined
                y_tfpminus_t       = _y _DCC tfp_minus time undefined
                y_tfpminus_tfpplus = _y _DCC tfp_minus tfp_plus undefined
                y_ipanx_t          = _y _DCC ipanx time undefined
                r_CNTRL            = _r _CNTRL

                ipanx_lt_t         = Cond (ValueLT ipanx time) _one _zero
                
            in dispatchStateTransition t continue (\ev -> \st -> case ev of 
                AD   -> _STF_AD_PAM st time y_sd_t
                IED  -> _STF_IED_PAM st time y_ipanx_t ipanx_lt_t y_sd_t 
                            (constntMaybe _IPNR)
                            _IPANX 
                            r_CNTRL 
                            (constntMaybe _IPAC) 
                            (constnt _NT)
                MD   -> _STF_MD_PAM st time
                PP   -> _STF_PP_PAM st time (useval "pp_payoff" t) y_sd_t y_tfpminus_t y_tfpminus_tfpplus 
                            (enum _FEB) 
                            (constnt _FER) 
                            r_CNTRL
                PY   -> _STF_PY_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus 
                            (enum _FEB)
                            (constnt _FER)
                            r_CNTRL
                FP   -> _STF_FP_PAM st time y_sd_t
                PRD  -> _STF_PRD_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus 
                            (enum _FEB) 
                            (constnt _FER) 
                            r_CNTRL 
                TD   -> _STF_IP_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus 
                            (enum _FEB) 
                            (constnt _FER) 
                            r_CNTRL 
                IP   -> _STF_IPCI_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus 
                            (enum _FEB) 
                            (constnt _FER) 
                            r_CNTRL
                IPCI -> _STF_IPCI_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus 
                            (enum _FEB) 
                            (constnt _FER) 
                            r_CNTRL
                RR   -> _STF_RR_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus 
                            (enum _FEB) 
                            (constnt _FER) 
                            r_CNTRL 
                            (constnt _RRLF) 
                            (constnt _RRLC) 
                            (constnt _RRPC) 
                            (constnt _RRPF) 
                            (constnt _RRMLT) 
                            (constnt _RRSP) 
                            (useval "o_rf_RRMO" t)
                RRF  -> _STF_RRF_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus 
                            (enum _FEB) 
                            (constnt _FER)
                            r_CNTRL 
                            (constntMaybe _RRNXT)
                SC   -> _STF_SC_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus 
                            (enum _FEB) 
                            (constnt _FER)
                            r_CNTRL 
                            _SCEF 
                            (useval "o_rf_SCMO" t) 
                            (constnt _SCIED)
                CE   -> _STF_CE_PAM st time y_sd_t
                _    -> st)
        LamContractTerms{..} -> undefined


     

    
     
    
     
    