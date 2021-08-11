module Language.Marlowe.ACTUS.Model.POF.PayoffModel where

import           Language.Marlowe.ACTUS.Definitions.ContractTerms (CR (..), FEB (FEB_A, FEB_N),
                                                                   PYTP (PYTP_A, PYTP_I, PYTP_N, PYTP_O))
import           Language.Marlowe.ACTUS.Ops                       (ActusNum (..), ActusOps (_max, _zero),
                                                                   RoleSignOps (_r))
import           Prelude                                          hiding (Fractional, Num, (*), (+), (-), (/))

-- Principal at Maturity (PAM)

_POF_IED_PAM :: (ActusNum a, ActusOps a, RoleSignOps a) => a -> CR -> a -> a -> a
_POF_IED_PAM o_rf_CURS _CNTRL _NT _PDIED = _zero - o_rf_CURS * _r _CNTRL * (_NT + _PDIED)

_POF_MD_PAM :: ActusNum a => a -> a -> a -> a -> a -> a -> a
_POF_MD_PAM o_rf_CURS nsc nt isct ipac feac = o_rf_CURS * (nsc * nt + isct * ipac + feac)

_POF_PP_PAM :: ActusNum a => a -> a -> a
_POF_PP_PAM o_rf_CURS pp_payoff = o_rf_CURS * pp_payoff

_POF_PY_PAM :: (ActusOps a, ActusNum a, RoleSignOps a) => PYTP -> a -> a -> a -> a -> CR -> a -> a -> a -> a
_POF_PY_PAM PYTP_A o_rf_CURS _         _PYRT _cPYRT _CNTRL _  _    _      = o_rf_CURS * _r _CNTRL * _PYRT
_POF_PY_PAM PYTP_N _         _         _PYRT _cPYRT _CNTRL _  _    _      = _cPYRT
_POF_PY_PAM PYTP_I o_rf_CURS o_rf_RRMO _PYRT _cPYRT _CNTRL nt ipnr y_sd_t = let c = o_rf_CURS * _r _CNTRL * y_sd_t * nt in  c * _max _zero (ipnr - o_rf_RRMO)
_POF_PY_PAM PYTP_O _         _         _PYRT _cPYRT _CNTRL _  _    _      = undefined -- FIXME: Ask Nils

_POF_FP_PAM :: (RoleSignOps a, ActusNum a) => FEB -> a -> a -> CR -> a -> a -> a -> a
_POF_FP_PAM FEB_A _FER o_rf_CURS _CNTRL _  _   _      = _r _CNTRL * o_rf_CURS * _FER
_POF_FP_PAM FEB_N _FER o_rf_CURS _CNTRL nt fac y_sd_t = o_rf_CURS * _FER * y_sd_t * nt * fac

_POF_PRD_PAM :: (ActusNum a, ActusOps a, RoleSignOps a) => a -> CR -> a -> a -> a -> a -> a -> a
_POF_PRD_PAM o_rf_CURS _CNTRL _PPRD ipac ipnr nt y_sd_t = _zero - o_rf_CURS * _r _CNTRL * (_PPRD + ipac + y_sd_t * ipnr * nt)

_POF_TD_PAM :: (ActusNum a, RoleSignOps a) => a -> CR -> a -> a -> a -> a -> a -> a
_POF_TD_PAM o_rf_CURS _CNTRL _PTD ipac ipnr nt y_sd_t = o_rf_CURS * _r _CNTRL * (_PTD + ipac + y_sd_t * ipnr * nt)

_POF_IP_PAM :: ActusNum a => a -> a -> a -> a -> a -> a -> a
_POF_IP_PAM o_rf_CURS isc ipac ipnr nt y_sd_t = o_rf_CURS * isc * (ipac + y_sd_t * ipnr * nt)

-- Linear Amortizer (LAM)

_POF_IED_LAM :: (ActusNum a, ActusOps a, RoleSignOps a) => a -> CR -> a -> a -> a
_POF_IED_LAM = _POF_IED_PAM

_POF_PR_LAM :: (ActusNum a, RoleSignOps a) => a -> CR -> a -> a -> a
_POF_PR_LAM o_rf_CURS _CNTRL nsc prnxt = o_rf_CURS * _r _CNTRL * nsc * prnxt

_POF_MD_LAM :: ActusNum a => a -> a -> a -> a -> a -> a -> a
_POF_MD_LAM = _POF_MD_PAM

_POF_PP_LAM :: ActusNum a => a -> a -> a
_POF_PP_LAM = _POF_PP_PAM

_POF_PY_LAM :: (ActusOps a, ActusNum a, RoleSignOps a) => PYTP -> a -> a -> a -> a -> CR -> a -> a -> a -> a
_POF_PY_LAM = _POF_PY_PAM

_POF_FP_LAM :: (RoleSignOps a, ActusNum a) => FEB -> a -> a -> CR -> a -> a -> a -> a
_POF_FP_LAM = _POF_FP_PAM

_POF_PRD_LAM :: (ActusNum a, ActusOps a, RoleSignOps a) => a -> CR -> a -> a -> a -> a -> a -> a
_POF_PRD_LAM o_rf_CURS _CNTRL _PPRD ipac ipnr ipcb y_sd_t = _zero - o_rf_CURS * _r _CNTRL * (_PPRD + ipac + y_sd_t * ipnr * ipcb)

_POF_TD_LAM :: (ActusNum a, RoleSignOps a) => a -> CR -> a -> a -> a -> a -> a -> a
_POF_TD_LAM o_rf_CURS _CNTRL _PTD ipac ipnr ipcb y_sd_t = o_rf_CURS * _r _CNTRL * (_PTD + ipac + y_sd_t * ipnr * ipcb)

_POF_IP_LAM :: ActusNum a => a -> a -> a -> a -> a -> a -> a
_POF_IP_LAM o_rf_CURS isc ipac ipnr ipcb y_sd_t = o_rf_CURS * isc * (ipac + y_sd_t * ipnr * ipcb)

-- Negative Amortizer (NAM)

_POF_IED_NAM :: (ActusNum a, ActusOps a, RoleSignOps a) => a -> CR -> a -> a -> a
_POF_IED_NAM = _POF_IED_PAM

_POF_PR_NAM :: ActusNum a => a -> a -> a -> a -> a -> a -> a -> a
_POF_PR_NAM o_rf_CURS nsc prnxt ipac y_sd_t ipnr ipcb = o_rf_CURS * nsc * (prnxt - ipac - y_sd_t * ipnr * ipcb)

_POF_MD_NAM :: ActusNum a => a -> a -> a -> a -> a -> a -> a
_POF_MD_NAM = _POF_MD_PAM

_POF_PP_NAM :: ActusNum a => a -> a -> a
_POF_PP_NAM = _POF_PP_PAM

_POF_PY_NAM :: (ActusOps a, ActusNum a, RoleSignOps a) => PYTP -> a -> a -> a -> a -> CR -> a -> a -> a -> a
_POF_PY_NAM = _POF_PY_PAM

_POF_FP_NAM :: (RoleSignOps a, ActusNum a) => FEB -> a -> a -> CR -> a -> a -> a -> a
_POF_FP_NAM = _POF_FP_PAM

_POF_PRD_NAM :: (ActusNum a, ActusOps a, RoleSignOps a) => a -> CR -> a -> a -> a -> a -> a -> a
_POF_PRD_NAM = _POF_PRD_LAM

_POF_TD_NAM :: (ActusNum a, RoleSignOps a) => a -> CR -> a -> a -> a -> a -> a -> a
_POF_TD_NAM = _POF_TD_LAM

_POF_IP_NAM :: ActusNum a => a -> a -> a -> a -> a -> a -> a
_POF_IP_NAM = _POF_IP_LAM
