{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.HP.STF.StateTransitionSpec where

import Language.Marlowe.ACTUS.HP.Utility.ContractRoleSign
import Language.Marlowe.ACTUS.HP.Utility.YearFraction
import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.ContractState
import Data.Time
import Data.Maybe

r = contractRoleSign
y = yearFraction

_STF_AD_PAM st@ContractState{..} t _DCC _MD = st {
    ipac = ipac + (y _DCC sd t _MD) * ipnr * nt,
    sd = t 
}

_STF_IED_PAM st@ContractState{..} t _DCC _MD _IPNR _IPANX _CNTRL _IPAC _NT = 
    let 
        yy = (y _DCC (fromJust _IPANX) t _MD)
        nt' = (r _CNTRL) * _NT
        ipnr' = if (isNothing _IPNR) then 0.0 else (fromJust _IPNR)
        ipac' = if (isJust _IPAC) then (fromJust _IPAC)
                else if (isJust _IPANX && (fromJust _IPANX) < t) then yy * nt' * ipnr'
                else 0.0
    in st { nt = nt', ipnr = ipnr', ipac = ipac', sd = t }

_STF_MD_PAM st@ContractState{..} t = st {
    nt = 0.0,
    ipac = 0.0,
    feac = 0.0,
    sd = t
}

_STF_PP_PAM st@ContractState{..} t pp_payoff _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL =
    let st' = _STF_PY_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL
    in st' {nt = nt - pp_payoff}

_STF_PY_PAM st@ContractState{..} t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL = 
    let
        ipac' = ipac + (y _DCC sd t _MD) * ipnr * nt
        fac' = case _FEB of 
            FEB_N -> fac + (y _DCC sd t _MD) * nt * _FER
            otherwise -> ((y _DCC tfp_minus t _MD) / (y _DCC tfp_minus tfp_plus _MD)) * (r _CNTRL) * _FER
    in st {ipac = ipac', fac = fac', sd = t}

_STF_FP_PAM st@ContractState{..} t _DCC _MD = st {
    ipac = ipac + (y _DCC sd t _MD) * ipnr * nt,
    fac = 0.0,
    sd = t 
}

_STF_PRD_PAM st@ContractState{..} t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL = 
    _STF_PY_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL

_STF_TD_PAM st@ContractState{..} t = st {
    nt = 0.0,
    ipac = 0.0,
    fac = 0.0,
    ipnr = 0.0,
    sd = t
}

_STF_IP_PAM st@ContractState{..} t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL = 
    let
        st' = _STF_PY_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL
    in st' {ipac = 0.0}

_STF_IPCI_PAM st@ContractState{..} t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL = 
    let
        st' = _STF_IP_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL
    in st' {nt = nt + ipac + (y _DCC sd t _MD) * nt * ipnr}


_STF_RR_PAM st@ContractState{..} t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL _RRLF _RRLC _RRPC _RRPF _RRMLT _RRSP o_rf_RRMO = 
    let
        st' = _STF_PRD_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL
        delta_r = (min (max (o_rf_RRMO * _RRMLT + _RRSP - ipnr) _RRPF) _RRPC)
        ipnr' = (min (max (ipnr + delta_r) _RRLF) _RRLC)
    in st' {ipnr = ipnr'}

_STF_RRF_PAM st@ContractState{..} t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL _RRNXT = 
    let
        st' = _STF_PRD_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL
    in st' {ipnr = fromMaybe 0.0 _RRNXT}

_STF_SC_PAM st@ContractState{..} t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL _SCEF o_rf_SCMO _SCIED = 
    let
        st' = _STF_PY_PAM st t _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL 
        nsc' = case _SCEF of 
            SE_00M -> nsc 
            SE_I00 -> nsc
            otherwise -> (o_rf_SCMO - _SCIED) / _SCIED
        isc' = case _SCEF of 
            SE_0N0 -> isc
            SE_00M -> isc 
            SE_0NM -> isc
            otherwise -> (o_rf_SCMO - _SCIED) / _SCIED
    in st' {nsc = nsc', isc = isc'}

_STF_CE_PAM st@ContractState{..} t _DCC _MD = _STF_AD_PAM st t _DCC _MD
