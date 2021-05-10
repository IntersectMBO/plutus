{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.POF.PayoffFs where

import           Data.Maybe                                        (fromJust)
import           Data.Time                                         (Day)
import           Language.Marlowe                                  (Observation, Value)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents (EventType (FP, IED, IP, MD, PP, PR, PRD, PY, TD))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms  (ContractTerms (..), ContractType (LAM, NAM, PAM))
import           Language.Marlowe.ACTUS.MarloweCompat              (constnt, enum, useval)
import           Language.Marlowe.ACTUS.Model.POF.PayoffModel
import           Language.Marlowe.ACTUS.Ops                        (ActusNum (..), YearFractionOps (_y),
                                                                    marloweFixedPoint)
import           Prelude                                           hiding (Fractional, Num, (*), (+), (-), (/))

payoffFs :: EventType -> ContractTerms -> Integer -> Integer -> Day -> Day -> Maybe (Value Observation)
payoffFs ev ContractTerms{..} t t_minus prevDate curDate =
    let __NT              = constnt (fromJust ct_NT)
        __PDIED           = constnt ct_PDIED
        __PYTP            = enum ct_PYTP
        __FEB             = enum ct_FEB
        __FER             = constnt ct_FER
        (__PPRD, __PTD  ) = (constnt (fromJust ct_PPRD), constnt (fromJust ct_PTD))
        (__PYRT, __cPYRT) = (constnt ct_PYRT, constnt ct_cPYRT)


        __o_rf_CURS       = useval "o_rf_CURS" t
        __o_rf_RRMO       = useval "o_rf_RRMO" t
        __pp_payoff       = useval "pp_payoff" t
        __nsc             = useval "nsc" t_minus
        __nt              = useval "nt" t_minus
        __isc             = useval "isc" t_minus
        __ipac            = useval "ipac" t_minus
        __feac            = useval "feac" t_minus
        __fac             = useval "fac" t_minus
        __ipnr            = useval "ipnr" t_minus
        __ipcb            = useval "ipcb" t_minus
        __prnxt           = useval "prnxt" t_minus

        y_sd_t            = constnt $ _y ct_DCC prevDate curDate ct_MD

        pof = case fromJust contractType of
            PAM -> case ev of
                IED -> Just $ _POF_IED_PAM __o_rf_CURS ct_CNTRL __NT __PDIED
                MD  -> Just $ _POF_MD_PAM __o_rf_CURS __nsc __nt __isc __ipac __feac
                PP  -> Just $ _POF_PP_PAM __o_rf_CURS __pp_payoff
                PY  -> Just $ _POF_PY_PAM __PYTP __o_rf_CURS __o_rf_RRMO __PYRT __cPYRT ct_CNTRL __nt __ipnr y_sd_t
                FP  -> Just $ _POF_FP_PAM __FEB __FER __o_rf_CURS ct_CNTRL __nt __fac y_sd_t
                PRD -> Just $ _POF_PRD_PAM __o_rf_CURS ct_CNTRL __PPRD __ipac __ipnr __nt y_sd_t
                TD  -> Just $ _POF_TD_PAM __o_rf_CURS ct_CNTRL __PTD __ipac __ipnr __nt y_sd_t
                IP  -> Just $ _POF_IP_PAM __o_rf_CURS __isc __ipac __ipnr __nt y_sd_t
                _   -> Nothing
            LAM -> case ev of
                IED -> Just $ _POF_IED_LAM __o_rf_CURS ct_CNTRL __NT __PDIED
                PR  -> Just $ _POF_PR_LAM __o_rf_CURS ct_CNTRL __nsc __prnxt
                MD  -> Just $ _POF_MD_LAM __o_rf_CURS __nsc __nt __isc __ipac __feac
                PP  -> Just $ _POF_PP_LAM __o_rf_CURS __pp_payoff
                PY  -> Just $ _POF_PY_LAM __PYTP __o_rf_CURS __o_rf_RRMO __PYRT __cPYRT ct_CNTRL __nt __ipnr y_sd_t
                FP  -> Just $ _POF_FP_LAM __FEB __FER __o_rf_CURS ct_CNTRL __nt __fac y_sd_t
                PRD -> Just $ _POF_PRD_LAM __o_rf_CURS ct_CNTRL __PPRD __ipac __ipnr __ipcb y_sd_t
                TD  -> Just $ _POF_TD_LAM __o_rf_CURS ct_CNTRL __PTD __ipac __ipnr __ipcb y_sd_t
                IP  -> Just $ _POF_IP_LAM __o_rf_CURS __isc __ipac __ipnr __ipcb y_sd_t
                _   -> Nothing
            NAM -> case ev of
                IED -> Just $ _POF_IED_NAM  __o_rf_CURS ct_CNTRL __NT __PDIED
                PR  -> Just $ _POF_PR_NAM __o_rf_CURS __nsc __prnxt __ipac y_sd_t __ipnr __ipcb
                MD  -> Just $ _POF_MD_NAM __o_rf_CURS __nsc __nt __isc __ipac __feac
                PP  -> Just $ _POF_PP_NAM __o_rf_CURS __pp_payoff
                PY  -> Just $ _POF_PY_NAM __PYTP __o_rf_CURS __o_rf_RRMO __PYRT __cPYRT ct_CNTRL __nt __ipnr y_sd_t
                FP  -> Just $ _POF_FP_NAM __FEB __FER __o_rf_CURS ct_CNTRL __nt __fac y_sd_t
                PRD -> Just $ _POF_PRD_NAM __o_rf_CURS ct_CNTRL __PPRD __ipac __ipnr __ipcb y_sd_t
                TD  -> Just $ _POF_TD_NAM __o_rf_CURS ct_CNTRL __PTD __ipac __ipnr __ipcb y_sd_t
                IP  -> Just $ _POF_IP_NAM __o_rf_CURS __isc __ipac __ipnr __ipcb y_sd_t
                _   -> Nothing
    in (\x -> x / (constnt $ fromIntegral marloweFixedPoint)) <$> pof
