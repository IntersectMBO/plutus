{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Language.Marlowe.ACTUS.Model.POF.PayoffModel where

import Language.Marlowe.ACTUS.Definitions.ContractTerms
    ( FEB(FEB_N, FEB_A), PYTP(PYTP_O, PYTP_A, PYTP_N, PYTP_I) )
import Language.Marlowe.ACTUS.Ops
    ( RoleSignOps(_r), ActusOps(_zero, _max) )

_POF_IED_PAM o_rf_CURS _CNTRL _NT _PDIED =
    -o_rf_CURS * _r _CNTRL * (_NT + _PDIED)

_POF_MD_PAM o_rf_CURS nsc nt isct ipac feac =
    o_rf_CURS * (nsc * nt + isct * ipac + feac)

_POF_PP_PAM o_rf_CURS pp_payoff = o_rf_CURS * pp_payoff

_POF_PY_PAM _PYTP o_rf_CURS o_rf_RRMO _PYRT _cPYRT _CNTRL nt ipnr y_sd_t =
    case _PYTP of
        PYTP_A -> o_rf_CURS * _r _CNTRL * _PYRT
        PYTP_N -> _cPYRT
        PYTP_I ->
            let c = o_rf_CURS * _r _CNTRL * y_sd_t * nt
            in  c * _max _zero (ipnr - o_rf_RRMO)
        PYTP_O -> undefined --todo ask Neils

_POF_FP_PAM _FEB _FER o_rf_CURS _CNTRL nt fac y_sd_t =
    let c = o_rf_CURS * _FER
    in  case _FEB of
            FEB_A -> _r _CNTRL * c
            FEB_N -> c * y_sd_t * nt * fac

_POF_PRD_PAM o_rf_CURS _CNTRL _PPRD ipac ipnr nt y_sd_t =
    -o_rf_CURS * _r _CNTRL * (_PPRD + ipac + y_sd_t * ipnr * nt)

_POF_TD_PAM o_rf_CURS _CNTRL _PTD ipac ipnr nt y_sd_t =
    o_rf_CURS * _r _CNTRL * (_PTD + ipac + y_sd_t * ipnr * nt)

_POF_IP_PAM o_rf_CURS isc ipac ipnr nt y_sd_t =
    o_rf_CURS * isc * (ipac + y_sd_t * ipnr * nt)

