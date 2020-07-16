{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.STF.StateTransitionFs (stateTransitionFs) where

import Data.Time ( Day )

import Language.Marlowe.ACTUS.Definitions.BusinessEvents
    ( EventType(..))

import Language.Marlowe.ACTUS.Model.STF.StateTransitionModel
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
import Language.Marlowe.ACTUS.Definitions.ContractTerms
    ( ContractTerms(..), ContractType(LAM, PAM), ScheduleConfig )
import Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator
    ( sup, inf )
import Language.Marlowe.ACTUS.Definitions.Schedule
    ( ShiftedDay(calculationDay) )
import Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule ( schedule )
import Language.Marlowe.ACTUS.Ops ( YearFractionOps(_y) )
import Data.Maybe ( fromJust, fromMaybe )

import Language.Marlowe.ACTUS.Model.Utility.DateShift

import Language.Marlowe(Contract)
import Language.Marlowe.ACTUS.MarloweCompat(constnt, marloweDate, enum, useval, stateTransitionMarlowe)

shift :: ScheduleConfig -> Day -> ShiftedDay
shift = applyBDCWithCfg

stateTransitionFs :: EventType -> ContractTerms -> Integer -> Day -> Contract -> Contract
stateTransitionFs ev terms@ContractTerms{..} t curDate continue = 
    let 
        -- value wrappers:
        __IPANX = marloweDate <$> _IPANX
        __IPNR  = constnt <$> _IPNR
        __IPAC  = constnt <$> _IPAC
        __NT    = constnt _NT
        __FEB   = enum _FEB
        __FER   = constnt _FER
        (__RRLF, __RRLC, __RRPC, __RRPF, __RRMLT, __RRSP) =
                ( constnt _RRLF
                , constnt _RRLC
                , constnt _RRPC
                , constnt _RRPF
                , constnt _RRMLT
                , constnt _RRSP
                )
        __RRNXT            = constnt <$> _RRNXT
        __SCIED            = constnt _SCIED
        __o_rf_RRMO        = useval "o_rf_RRMO" t
        __o_rf_SCMO        = useval "o_rf_SCMO" t
        __pp_payoff        = useval "pp_payoff" t

        -- dates:
        time               = marloweDate $ curDate
        fpSchedule         = fromMaybe [shift scfg _SD] $ schedule FP terms
        tfp_minus          = calculationDay $ sup fpSchedule curDate
        tfp_plus           = calculationDay $ inf fpSchedule curDate
        y_sd_t             = constnt $ _y _DCC _SD curDate _MD
        y_tfpminus_t       = constnt $ _y _DCC tfp_minus curDate _MD
        y_tfpminus_tfpplus = constnt $ _y _DCC tfp_minus tfp_plus _MD
        y_ipanx_t          = constnt $ _y _DCC (fromJust _IPANX) curDate _MD
                        
    in case contractType of
        PAM -> 
            stateTransitionMarlowe ev t continue $ \event st -> case event of 
                AD   -> _STF_AD_PAM st time y_sd_t
                IED  -> _STF_IED_PAM st time y_ipanx_t __IPNR __IPANX _CNTRL __IPAC __NT
                MD   -> _STF_MD_PAM st time
                PP   -> _STF_PP_PAM st time __pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER _CNTRL
                PY   -> _STF_PY_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER _CNTRL
                FP   -> _STF_FP_PAM st time y_sd_t
                PRD  -> _STF_PRD_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER _CNTRL 
                TD   -> _STF_IP_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER _CNTRL 
                IP   -> _STF_IPCI_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER _CNTRL
                IPCI -> _STF_IPCI_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER _CNTRL
                RR   -> _STF_RR_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER _CNTRL __RRLF __RRLC __RRPC __RRPF __RRMLT __RRSP __o_rf_RRMO
                RRF  -> _STF_RRF_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER _CNTRL __RRNXT
                SC   -> _STF_SC_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER _CNTRL _SCEF __o_rf_SCMO __SCIED
                CE   -> _STF_CE_PAM st time y_sd_t
                _    -> st
        LAM -> undefined

