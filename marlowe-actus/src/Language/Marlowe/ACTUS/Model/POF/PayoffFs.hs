{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.POF.PayoffFs where

import           Data.Time                                         (Day)
import           Language.Marlowe                                  (Observation, Value)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents (EventType (FP, IED, IP, MD, PP, PRD, PY, TD))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms  (ContractTerms (..), ContractType (LAM, PAM))
import           Language.Marlowe.ACTUS.MarloweCompat              (constnt, enum, useval)
import           Language.Marlowe.ACTUS.Model.POF.PayoffModel      (_POF_FP_PAM, _POF_IED_PAM, _POF_IP_PAM, _POF_MD_PAM,
                                                                    _POF_PP_PAM, _POF_PRD_PAM, _POF_PY_PAM, _POF_TD_PAM)
import           Language.Marlowe.ACTUS.Ops                        (YearFractionOps (_y))

payoffFs :: EventType -> ContractTerms -> Integer -> Day -> Value Observation
payoffFs ev ContractTerms{..} t curDate =
    let __NT              = constnt ct_NT
        __PDIED           = constnt ct_PDIED
        __PYTP            = enum ct_PYTP
        __FEB             = enum ct_FEB
        __FER             = constnt ct_FER
        (__PPRD, __PTD  ) = (constnt ct_PPRD, constnt ct_PTD)
        (__PYRT, __cPYRT) = (constnt ct_PYRT, constnt ct_cPYRT)


        __o_rf_CURS       = useval "o_rf_CURS" t
        __o_rf_RRMO       = useval "o_rf_RRMO" t
        __pp_payoff       = useval "pp_payoff" t
        __nsc             = useval "nsc" t
        __nt              = useval "nt" t
        __isc             = useval "isc" t
        __ipac            = useval "ipac" t
        __feac            = useval "feac" t
        __fac             = useval "fac" t
        __ipnr            = useval "ipnr" t

        y_sd_t = constnt $ _y ct_DCC ct_SD curDate undefined

    in case contractType of
        PAM -> case ev of
            IED -> _POF_IED_PAM __o_rf_CURS ct_CNTRL __NT __PDIED
            MD  -> _POF_MD_PAM __o_rf_CURS __nsc __nt __isc __ipac __feac
            PP  -> _POF_PP_PAM __o_rf_CURS __pp_payoff
            PY  -> _POF_PY_PAM __PYTP __o_rf_CURS __o_rf_RRMO __PYRT __cPYRT ct_CNTRL __nt __ipnr y_sd_t
            FP  -> _POF_FP_PAM __FEB __FER __o_rf_CURS ct_CNTRL __nt __fac y_sd_t
            PRD -> _POF_PRD_PAM __o_rf_CURS ct_CNTRL __PPRD __ipac __ipnr __nt y_sd_t
            TD  -> _POF_TD_PAM __o_rf_CURS ct_CNTRL __PTD __ipac __ipnr __nt y_sd_t
            IP  -> _POF_IP_PAM __o_rf_CURS __isc __ipac __ipnr __nt y_sd_t
            _   -> constnt 0
        LAM -> undefined

