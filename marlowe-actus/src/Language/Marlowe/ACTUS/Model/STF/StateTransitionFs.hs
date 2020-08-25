{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.STF.StateTransitionFs (stateTransitionFs) where

import           Data.Time                                              (Day)

import           Language.Marlowe.ACTUS.Definitions.BusinessEvents      (EventType (..))

import           Data.Maybe                                             (fromJust, fromMaybe)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (ContractTerms (..), ContractType (LAM, PAM))
import           Language.Marlowe.ACTUS.Definitions.Schedule            (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule    (schedule)
import           Language.Marlowe.ACTUS.Model.STF.StateTransitionModel  (_STF_AD_PAM, _STF_CE_PAM, _STF_FP_PAM,
                                                                         _STF_IED_PAM, _STF_IPCI_PAM, _STF_IP_PAM,
                                                                         _STF_MD_PAM, _STF_PP_PAM, _STF_PRD_PAM,
                                                                         _STF_PY_PAM, _STF_RRF_PAM, _STF_RR_PAM,
                                                                         _STF_SC_PAM, _STF_TD_PAM)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (inf, sup)
import           Language.Marlowe.ACTUS.Ops                             (YearFractionOps (_y))

import           Language.Marlowe                                       (Contract)
import           Language.Marlowe.ACTUS.MarloweCompat                   (constnt, enum, letval, marloweDate,
                                                                         stateTransitionMarlowe, useval)


stateTransitionFs :: EventType -> ContractTerms -> Integer -> Day -> Day -> Contract -> Contract
stateTransitionFs ev terms@ContractTerms{..} t prevDate curDate continue =
    let
        -- value wrappers:
        __IPANX = marloweDate <$> ct_IPANX
        __IPNR  = constnt <$> ct_IPNR
        __IPAC  = constnt <$> ct_IPAC
        __NT    = constnt ct_NT
        __FEB   = enum ct_FEB
        __FER   = constnt ct_FER
        (__RRLF, __RRLC, __RRPC, __RRPF, __RRMLT, __RRSP) =
                ( constnt ct_RRLF
                , constnt ct_RRLC
                , constnt ct_RRPC
                , constnt ct_RRPF
                , constnt ct_RRMLT
                , constnt ct_RRSP
                )
        __RRNXT            = constnt <$> ct_RRNXT
        __SCIED            = constnt ct_SCIED
        __o_rf_RRMO        = useval "o_rf_RRMO" t
        __o_rf_SCMO        = useval "o_rf_SCMO" t
        __pp_payoff        = useval "pp_payoff" t

        -- dates:
        time               = marloweDate $ curDate
        fpSchedule         = schedule FP terms
        tfp_minus          = fromMaybe curDate $ calculationDay <$> ((\sc -> sup sc curDate) =<< fpSchedule)
        tfp_plus           = fromMaybe curDate $ calculationDay <$> ((\sc -> inf sc curDate) =<< fpSchedule)
        y_tfpminus_t       = constnt $ _y ct_DCC tfp_minus curDate ct_MD
        y_tfpminus_tfpplus = constnt $ _y ct_DCC tfp_minus tfp_plus ct_MD
        y_ipanx_t          = constnt $ _y ct_DCC (fromJust ct_IPANX) curDate ct_MD
        y_sd_t             = constnt $ _y ct_DCC prevDate curDate ct_MD

        addComment cont    = case ev of
            IED -> letval "IED" t (constnt 0) cont
            MD  -> letval "MD" t (constnt 0) cont
            IP  -> letval ("IP:" ++ (show curDate) ++ (show prevDate)) t (constnt 0) cont
            RR  -> letval ("RR:" ++ (show curDate)) t (constnt 0) cont
            FP  -> letval ("FP:" ++ (show curDate)) t (constnt 0) cont
            _   -> cont
    in case contractType of
        PAM ->
            addComment $ stateTransitionMarlowe ev t continue $ \event st ->
                case event of
                    AD   -> _STF_AD_PAM st time y_sd_t
                    IED  -> _STF_IED_PAM st time y_ipanx_t __IPNR __IPANX ct_CNTRL __IPAC __NT
                    MD   -> _STF_MD_PAM st time
                    PP   -> _STF_PP_PAM st time __pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER ct_CNTRL
                    PY   -> _STF_PY_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER ct_CNTRL
                    FP   -> _STF_FP_PAM st time y_sd_t
                    PRD  -> _STF_PRD_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER ct_CNTRL
                    TD   -> _STF_TD_PAM st time
                    IP   -> _STF_IP_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER ct_CNTRL
                    IPCI -> _STF_IPCI_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER ct_CNTRL
                    RR   -> _STF_RR_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER ct_CNTRL __RRLF __RRLC __RRPC __RRPF __RRMLT __RRSP __o_rf_RRMO
                    RRF  -> _STF_RRF_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER ct_CNTRL __RRNXT
                    SC   -> _STF_SC_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus __FEB __FER ct_CNTRL ct_SCEF __o_rf_SCMO __SCIED
                    CE   -> _STF_CE_PAM st time y_sd_t
                    _    -> st
        LAM -> undefined

