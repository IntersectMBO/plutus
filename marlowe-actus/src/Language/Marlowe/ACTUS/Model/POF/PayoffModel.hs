module Language.Marlowe.ACTUS.Model.POF.PayoffModel where

import           Language.Marlowe.ACTUS.Definitions.ContractTerms (CR (..), FEB (FEB_A, FEB_N),
                                                                   PYTP (PYTP_A, PYTP_I, PYTP_N, PYTP_O))
import           Language.Marlowe.ACTUS.Ops                       (ActusNum (..), ActusOps (_abs, _max, _zero),
                                                                   RoleSignOps (_r))
import           Prelude                                          hiding (Fractional, Num, (*), (+), (-), (/))

-- Principal at Maturity (PAM)

_POF_IED_PAM :: RoleSignOps a => a -> CR -> a -> a -> a
_POF_IED_PAM o_rf_CURS _CNTRL _NT _PDIED = _zero - o_rf_CURS * _r _CNTRL * (_NT + _PDIED)

_POF_MD_PAM :: ActusNum a => a -> a -> a -> a -> a -> a -> a
_POF_MD_PAM o_rf_CURS nsc nt isct ipac feac = o_rf_CURS * (nsc * nt + isct * ipac + feac)

_POF_PP_PAM :: ActusNum a => a -> a -> a
_POF_PP_PAM o_rf_CURS pp_payoff = o_rf_CURS * pp_payoff

_POF_PY_PAM :: RoleSignOps a => PYTP -> a -> a -> a -> CR -> a -> a -> a -> a
_POF_PY_PAM PYTP_A o_rf_CURS _ _PYRT _CNTRL _ _ _ = o_rf_CURS * _r _CNTRL * _PYRT
_POF_PY_PAM PYTP_N o_rf_CURS _ _PYRT _CNTRL nt _ y_sd_t = let c = o_rf_CURS * _r _CNTRL * y_sd_t * nt in  c * _PYRT
_POF_PY_PAM PYTP_I o_rf_CURS o_rf_RRMO _PYRT _CNTRL nt ipnr y_sd_t = let c = o_rf_CURS * _r _CNTRL * y_sd_t * nt in  c * _max _zero (ipnr - o_rf_RRMO)
_POF_PY_PAM PYTP_O _ _ _ _ _ _ _ = undefined -- FIXME: Ask Nils

_POF_FP_PAM :: RoleSignOps a => FEB -> a -> a -> CR -> a -> a -> a -> a
_POF_FP_PAM FEB_A _FER o_rf_CURS _CNTRL _  _   _      = _r _CNTRL * o_rf_CURS * _FER
_POF_FP_PAM FEB_N _FER o_rf_CURS _CNTRL nt fac y_sd_t = o_rf_CURS * _FER * y_sd_t * nt * fac

_POF_PRD_PAM :: RoleSignOps a => a -> CR -> a -> a -> a -> a -> a -> a
_POF_PRD_PAM o_rf_CURS _CNTRL _PPRD ipac ipnr nt y_sd_t = _zero - o_rf_CURS * _r _CNTRL * (_PPRD + ipac + y_sd_t * ipnr * nt)

_POF_TD_PAM :: RoleSignOps a => a -> CR -> a -> a -> a -> a -> a -> a
_POF_TD_PAM o_rf_CURS _CNTRL _PTD ipac ipnr nt y_sd_t = o_rf_CURS * _r _CNTRL * (_PTD + ipac + y_sd_t * ipnr * nt)

_POF_IP_PAM :: ActusNum a => a -> a -> a -> a -> a -> a -> a
_POF_IP_PAM o_rf_CURS isc ipac ipnr nt y_sd_t = o_rf_CURS * isc * (ipac + y_sd_t * ipnr * nt)

-- Linear Amortizer (LAM)

_POF_PR_LAM :: RoleSignOps a => a -> CR -> a -> a -> a -> a
_POF_PR_LAM o_rf_CURS _CNTRL nt nsc prnxt =
  let redemption = prnxt - _r _CNTRL * _max _zero (_abs prnxt - _abs nt)
   in o_rf_CURS * _r _CNTRL * nsc * redemption

_POF_PRD_LAM :: RoleSignOps a => a -> CR -> a -> a -> a -> a -> a -> a
_POF_PRD_LAM o_rf_CURS _CNTRL _PPRD ipac ipnr ipcb y_sd_t = _zero - o_rf_CURS * _r _CNTRL * (_PPRD + ipac + y_sd_t * ipnr * ipcb)

_POF_TD_LAM :: RoleSignOps a => a -> CR -> a -> a -> a -> a -> a -> a
_POF_TD_LAM o_rf_CURS _CNTRL _PTD ipac ipnr ipcb y_sd_t = o_rf_CURS * _r _CNTRL * (_PTD + ipac + y_sd_t * ipnr * ipcb)

_POF_IP_LAM :: ActusNum a => a -> a -> a -> a -> a -> a -> a
_POF_IP_LAM o_rf_CURS isc ipac ipnr ipcb y_sd_t = o_rf_CURS * isc * (ipac + y_sd_t * ipnr * ipcb)

-- Negative Amortizer (NAM)

_POF_PR_NAM :: RoleSignOps a => a -> CR -> a -> a -> a -> a -> a -> a -> a -> a
_POF_PR_NAM o_rf_CURS _CNTRL nsc prnxt ipac y_sd_t ipnr ipcb nt =
  let ra = prnxt - _r _CNTRL * (ipac + y_sd_t * ipnr * ipcb)
      r = ra - _max _zero (ra - _abs nt)
   in o_rf_CURS * _r _CNTRL * nsc * r
