{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.STF.StateTransition where

import           Data.Time                                              (Day)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents      (EventType (..), RiskFactors (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState       (ContractState, ContractStatePoly (ContractStatePoly, fac, feac, ipac, ipcb, ipnr, isc, nsc, nt, prf, prnxt, sd, tmd))

import           Data.Maybe                                             (fromJust, fromMaybe)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (ContractTerms (..), ContractType (LAM, PAM),
                                                                         ScheduleConfig)
import           Language.Marlowe.ACTUS.Definitions.Schedule            (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule    (schedule)
import           Language.Marlowe.ACTUS.Model.STF.StateTransitionModel  (_STF_AD_PAM, _STF_CE_PAM, _STF_FP_PAM,
                                                                         _STF_IED_PAM, _STF_IPCI_PAM, _STF_IP_PAM,
                                                                         _STF_MD_PAM, _STF_PP_PAM, _STF_PRD_PAM,
                                                                         _STF_PY_PAM, _STF_RRF_PAM, _STF_RR_PAM,
                                                                         _STF_SC_PAM)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (inf, sup)
import           Language.Marlowe.ACTUS.Ops                             (YearFractionOps (_y))


import           Language.Marlowe.ACTUS.Model.Utility.DateShift

shift :: ScheduleConfig -> Day -> ShiftedDay
shift = applyBDCWithCfg

stateTransition :: EventType -> RiskFactors -> ContractTerms -> ContractState -> Day -> ContractState
stateTransition ev RiskFactors{..} terms@ContractTerms{..} st@ContractStatePoly{..} t =
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
                AD   -> _STF_AD_PAM st t y_sd_t
                IED  -> _STF_IED_PAM st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
                MD   -> _STF_MD_PAM st t
                PP   -> _STF_PP_PAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
                PY   -> _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
                FP   -> _STF_FP_PAM st t y_sd_t
                PRD  -> _STF_PRD_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
                TD   -> _STF_IP_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
                IP   -> _STF_IPCI_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
                IPCI -> _STF_IPCI_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
                RR   -> _STF_RR_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRLF _RRLC _RRPC _RRPF _RRMLT _RRSP o_rf_RRMO
                RRF  -> _STF_RRF_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRNXT
                SC   -> _STF_SC_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _SCEF o_rf_SCMO _SCIED
                CE   -> _STF_CE_PAM st t y_sd_t
                _    -> st
        LAM -> undefined









