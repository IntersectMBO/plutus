module Language.Marlowe.ACTUS.HP.POF.PAM where

import Language.Marlowe.ACTUS.HP.Utility.ContractRoleSign
import Language.Marlowe.ACTUS.HP.Utility.YearFraction
import Language.Marlowe.ACTUS.HP.ContractTerms
import Data.Time

r = contractRoleSign
y = yearFraction

_POF_AD_PAM = 0.0

_POF_IED_PAM o_rf_CURS _CNTRL _NT _PDIED = o_rf_CURS * (r _CNTRL) * (-1) * (_NT + _PDIED)

_POF_MD_PAM o_rf_CURS nsc nt isct ipac feac = o_rf_CURS * (nsc * nt + isct * ipac + feac)

_POF_PP_PAM o_rf_CURS pp_payoff = o_rf_CURS * pp_payoff

_POF_PY_PAM _PYTP o_rf_CURS o_rf_rrmo _PYRT _cPYRT _CNTRL nt _DCC sd t _MD ipnr = case _PYTP of
    PYTP_A -> o_rf_CURS * (r _CNTRL) * _PYRT
    PYTP_N -> _cPYRT
    PYTP_I -> let c = o_rf_CURS * (r _CNTRL) * (y _DCC sd t _MD) * nt
          in c * (max 0 (ipnr - o_rf_rrmo))

_POF_FP_PAM _FEB _FER o_rf_CURS _CNTRL _DCC sd t _MD nt fac = 
    let c = o_rf_CURS * _FER in
        case _FEB of
            FEB_A -> (r _CNTRL) * c
            FEB_N -> c * (y _DCC sd t _MD) * nt * fac

_POF_PRD_PAM o_rf_CURS _CNTRL _PPRD ipac _DCC sd t _MD ipnr nt =
    o_rf_CURS * (r _CNTRL) * (-1) * (_PPRD + ipac + (y _DCC sd t _MD) * ipnr * nt)

_POF_TD_PAM o_rf_CURS _CNTRL _PTD ipac _DCC sd t _MD ipnr nt = 
    o_rf_CURS * (r _CNTRL) * (_PTD + ipac + (y _DCC sd t _MD) * ipnr * nt)

_POF_IP_PAM o_rf_CURS isc ipac _DCC sd t _MD ipnr nt = 
    o_rf_CURS * isc * (ipac + (y _DCC sd t _MD) * ipnr * nt)

_POF_IPCI_PAM = 0.0

_POF_RR_PAM = 0.0

_POF_RRF_PAM = 0.0

_POF_SC_PAM = 0.0

_POF_CE_PAM = 0.0
