{-# OPTIONS_GHC -fno-warn-missing-signatures #-} 
module Language.Marlowe.ACTUS.POF.PayoffSpec where

import Language.Marlowe.ACTUS.ContractTerms
import Language.Marlowe.ACTUS.Ops

_POF_IED_PAM o_rf_CURS r_CNTRL _NT _PDIED = 
    - o_rf_CURS * r_CNTRL * (_NT + _PDIED)

_POF_MD_PAM o_rf_CURS nsc nt isct ipac feac = 
    o_rf_CURS * (nsc * nt + isct * ipac + feac)

_POF_PP_PAM o_rf_CURS pp_payoff = 
    o_rf_CURS * pp_payoff

_POF_PY_PAM _PYTP o_rf_CURS o_rf_RRMO _PYRT _cPYRT r_CNTRL nt ipnr y_sd_t = 
    case _PYTP of
        PYTP_A -> o_rf_CURS * r_CNTRL * _PYRT
        PYTP_N -> _cPYRT
        PYTP_I -> let c = o_rf_CURS * r_CNTRL * y_sd_t * nt
                 in c * (_max _zero (ipnr - o_rf_RRMO))

_POF_FP_PAM _FEB _FER o_rf_CURS r_CNTRL nt fac y_sd_t = 
    let c = o_rf_CURS * _FER in
        case _FEB of
            FEB_A -> r_CNTRL * c
            FEB_N -> c * y_sd_t * nt * fac

_POF_PRD_PAM o_rf_CURS r_CNTRL _PPRD ipac ipnr nt y_sd_t =
    - o_rf_CURS * r_CNTRL * (_PPRD + ipac + y_sd_t * ipnr * nt)

_POF_TD_PAM o_rf_CURS r_CNTRL _PTD ipac ipnr nt y_sd_t = 
    o_rf_CURS * r_CNTRL * (_PTD + ipac + y_sd_t * ipnr * nt)

_POF_IP_PAM o_rf_CURS isc ipac ipnr nt y_sd_t = 
    o_rf_CURS * isc * (ipac + y_sd_t * ipnr * nt)

