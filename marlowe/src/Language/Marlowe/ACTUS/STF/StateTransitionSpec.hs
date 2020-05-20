{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.STF.StateTransitionSpec where

import Language.Marlowe.ACTUS.ContractTerms
import Language.Marlowe.ACTUS.ContractState
import Data.Maybe

zero :: forall a. Num a => a
zero = fromInteger 0

_STF_AD_PAM st@ContractStatePoly{..} t y_sd_t = st {
    ipac = ipac + y_sd_t * ipnr * nt,
    sd = t 
}

_STF_IED_PAM st@ContractStatePoly{..} t y_ipanx_t ipanx_LT_t y_sd_t _IPNR _IPANX r_CNTRL _IPAC _NT = 
    let 
        nt' = r_CNTRL * _NT
        ipnr' = if (isNothing _IPNR) then zero else (fromJust _IPNR)
        ipac' = if (isJust _IPAC) then (fromJust _IPAC)
                else if (isJust _IPANX && ipanx_LT_t) then y_ipanx_t * nt' * ipnr'
                else zero
    in st { nt = nt', ipnr = ipnr', ipac = ipac', sd = t }

_STF_MD_PAM st@ContractStatePoly{..} t = st {
    nt = zero,
    ipac = zero,
    feac = zero,
    sd = t
}

_STF_PP_PAM st@ContractStatePoly{..} t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL =
    let st' = _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL
    in st' {nt = nt - pp_payoff}

_STF_PY_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL = 
    let
        ipac' = ipac + y_sd_t * ipnr * nt
        fac' = case _FEB of 
            FEB_N -> fac + y_sd_t * nt * _FER
            _ -> (y_tfpminus_t / y_tfpminus_tfpplus) * r_CNTRL * _FER
    in st {ipac = ipac', fac = fac', sd = t}

_STF_FP_PAM st@ContractStatePoly{..} t y_sd_t = st {
    ipac = ipac + y_sd_t * ipnr * nt,
    fac = zero,
    sd = t 
}

_STF_PRD_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL = 
    _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL

_STF_TD_PAM st@ContractStatePoly{..} t = st {
    nt = zero,
    ipac = zero,
    fac = zero,
    ipnr = zero,
    sd = t
}

_STF_IP_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL = 
    let
        st' = _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL
    in st' {ipac = zero}

_STF_IPCI_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL = 
    let
        st' = _STF_IP_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL
    in st' {nt = nt + ipac + y_sd_t * nt * ipnr}


_STF_RR_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL _RRLF _RRLC _RRPC _RRPF _RRMLT _RRSP o_rf_RRMO = 
    let
        st' = _STF_PRD_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL
        delta_r = (min (max (o_rf_RRMO * _RRMLT + _RRSP - ipnr) _RRPF) _RRPC)
        ipnr' = (min (max (ipnr + delta_r) _RRLF) _RRLC)
    in st' {ipnr = ipnr'}

_STF_RRF_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL _RRNXT = 
    let
        st' = _STF_PRD_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL
    in st' {ipnr = fromMaybe zero _RRNXT}

_STF_SC_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL _SCEF o_rf_SCMO _SCIED = 
    let
        st' = _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER r_CNTRL 
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

_STF_CE_PAM st@ContractStatePoly{..} t y_sd_t = _STF_AD_PAM st t y_sd_t
