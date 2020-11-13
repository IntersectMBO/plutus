{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.STF.StateTransition where

import           Data.Time                                              (Day)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents      (EventType (..), RiskFactors (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState       (ContractState,
                                                                         ContractStatePoly (ContractStatePoly, fac, feac, ipac, ipcb, ipnr, isc, nsc, nt, prf, prnxt, sd, tmd))

import           Data.Maybe                                             (fromJust, fromMaybe)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (ContractTerms (..), ContractType (LAM, PAM),
                                                                         ScheduleConfig)
import           Language.Marlowe.ACTUS.Definitions.Schedule            (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule    (schedule)
import           Language.Marlowe.ACTUS.Model.STF.StateTransitionModel  (_STF_AD_PAM, _STF_CE_PAM, _STF_FP_PAM,
                                                                         _STF_IED_PAM, _STF_IPCI_PAM, _STF_IP_PAM,
                                                                         _STF_MD_PAM, _STF_PP_PAM, _STF_PRD_PAM,
                                                                         _STF_PY_PAM, _STF_RRF_PAM, _STF_RR_PAM,
                                                                         _STF_SC_PAM, _STF_TD_PAM)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (inf, sup)
import           Language.Marlowe.ACTUS.Ops                             (YearFractionOps (_y))


import           Language.Marlowe.ACTUS.Model.Utility.DateShift

shift :: ScheduleConfig -> Day -> ShiftedDay
shift = applyBDCWithCfg

stateTransition :: EventType -> RiskFactors -> ContractTerms -> ContractState -> Day -> ContractState
stateTransition ev RiskFactors{..} terms@ContractTerms{..} st@ContractStatePoly{..} t =
    let
        fpSchedule         = schedule FP terms
        tfp_minus          = fromMaybe t $ calculationDay <$> ((\sc -> sup sc t) =<< fpSchedule)
        tfp_plus           = fromMaybe t $ calculationDay <$> ((\sc -> inf sc t) =<< fpSchedule)
        y_sd_t             = _y ct_DCC sd t ct_MD
        y_tfpminus_t       = _y ct_DCC tfp_minus t ct_MD
        y_tfpminus_tfpplus = _y ct_DCC tfp_minus tfp_plus ct_MD
        y_ipanx_t          = _y ct_DCC (fromJust ct_IPANX) t ct_MD
    in case contractType of
        PAM ->
            case ev of
                AD   -> _STF_AD_PAM st t y_sd_t
                IED  -> _STF_IED_PAM st t y_ipanx_t ct_IPNR ct_IPANX ct_CNTRL ct_IPAC ct_NT
                MD   -> _STF_MD_PAM st t
                PP   -> _STF_PP_PAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB ct_FER ct_CNTRL
                PY   -> _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB ct_FER ct_CNTRL
                FP   -> _STF_FP_PAM st t y_sd_t
                PRD  -> _STF_PRD_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB ct_FER ct_CNTRL
                TD   -> _STF_TD_PAM st t
                IP   -> _STF_IP_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB ct_FER ct_CNTRL
                IPCI -> _STF_IPCI_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB ct_FER ct_CNTRL
                RR   -> _STF_RR_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB ct_FER ct_CNTRL ct_RRLF ct_RRLC ct_RRPC ct_RRPF ct_RRMLT ct_RRSP o_rf_RRMO
                RRF  -> _STF_RRF_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB ct_FER ct_CNTRL ct_RRNXT
                SC   -> _STF_SC_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB ct_FER ct_CNTRL ct_SCEF o_rf_SCMO ct_SCIED
                CE   -> _STF_CE_PAM st t y_sd_t
                _    -> st
        LAM -> undefined
