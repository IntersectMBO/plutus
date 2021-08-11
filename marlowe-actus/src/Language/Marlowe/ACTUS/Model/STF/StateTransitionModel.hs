{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.STF.StateTransitionModel where

import           Data.Maybe                                       (fromJust, fromMaybe, isJust, isNothing)
import           Language.Marlowe.ACTUS.Definitions.ContractState (ContractStatePoly (ContractStatePoly, fac, feac, ipac, ipcb, ipnr, isc, nsc, nt, prf, prnxt, sd, tmd))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms (CR, FEB (FEB_N), IPCB (IPCB_NT),
                                                                   SCEF (SE_00M, SE_0N0, SE_0NM, SE_I00))
import           Language.Marlowe.ACTUS.Ops                       (ActusNum (..), ActusOps (_max, _min, _zero),
                                                                   DateOps (_lt), RoleSignOps (_r))
import           Prelude                                          hiding (Fractional, Num, (*), (+), (-), (/))

-- Principal at Maturity
_STF_AD_PAM :: ActusNum a => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_AD_PAM st@ContractStatePoly{..} t y_sd_t = st {
    ipac = ipac + y_sd_t * ipnr * nt,
    sd = t
}

_STF_IED_PAM :: (RoleSignOps a1, ActusNum a1, DateOps a2 a1, ActusOps a1) => ContractStatePoly a1 a2 -> a2 -> a1 -> Maybe a1 -> Maybe a2 -> CR -> Maybe a1 -> a1 -> ContractStatePoly a1 a2
_STF_IED_PAM st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT =
    let
        nt'                         = _r _CNTRL * _NT
        ipnr' | isNothing _IPNR     = _zero
              | otherwise           = fromJust _IPNR

        ipac' | isJust _IPAC        = fromJust _IPAC
              | isJust _IPANX       = _lt (fromJust _IPANX) t * y_ipanx_t * nt' * ipnr'
              | otherwise           = _zero
    in st { nt = nt', ipnr = ipnr', ipac = ipac', sd = t }

_STF_MD_PAM :: ActusOps a => ContractStatePoly a b -> b -> ContractStatePoly a b
_STF_MD_PAM st t = st {
    nt = _zero,
    ipac = _zero,
    feac = _zero,
    sd = t
}

_STF_PP_PAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_PP_PAM st@ContractStatePoly{..} t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL =
    let st' = _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
    in st' {nt = nt - pp_payoff}

_STF_PY_PAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_PY_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL =
    let
        ipac' = ipac + y_sd_t * ipnr * nt

        fac' = case _FEB of
            Just FEB_N -> fac + y_sd_t * nt * _FER
            _          -> y_tfpminus_t / y_tfpminus_tfpplus * _r _CNTRL * _FER

    in st {ipac = ipac', fac = fac', sd = t}

_STF_FP_PAM :: (ActusNum a, ActusOps a) => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_FP_PAM st@ContractStatePoly{..} t y_sd_t = st {
    ipac = ipac + y_sd_t * ipnr * nt,
    fac = _zero,
    sd = t
}

_STF_PRD_PAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_PRD_PAM = _STF_PY_PAM

_STF_TD_PAM :: ActusOps a => ContractStatePoly a b -> b -> ContractStatePoly a b
_STF_TD_PAM st t = st {
    nt = _zero,
    ipac = _zero,
    fac = _zero,
    ipnr = _zero,
    sd = t
}

_STF_IP_PAM :: (ActusOps a, RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_IP_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL =
    let
        st' = _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
    in st' {
        ipac = _zero
    }

_STF_IPCI_PAM :: (ActusOps a, RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_IPCI_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL =
    let
        st' = _STF_IP_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
    in st' {
        nt = nt + ipac + y_sd_t * nt * ipnr
    }

_STF_RR_PAM :: (ActusOps a, RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> a -> a -> a -> a -> a -> a -> a -> ContractStatePoly a b
_STF_RR_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRLF _RRLC _RRPC _RRPF _RRMLT _RRSP o_rf_RRMO =
    let
        ipac' = ipac + y_sd_t * ipnr * nt
        fac'  =
          case _FEB of
            Just FEB_N -> fac + y_sd_t * nt * _FER
            _          -> y_tfpminus_t / y_tfpminus_tfpplus * _r _CNTRL * _FER

        st' = _STF_PRD_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL

        delta_r = _min (_max (o_rf_RRMO * _RRMLT + _RRSP - ipnr) _RRPF) _RRPC

        ipnr' = _min (_max (ipnr + delta_r) _RRLF) _RRLC
    in st' {ipac = ipac', fac = fac', ipnr = ipnr', sd = t}

_STF_RRF_PAM :: (ActusOps a, RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe a -> ContractStatePoly a b
_STF_RRF_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRNXT =
    let
        st' = _STF_PRD_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
    in st' {
        ipnr = fromMaybe _zero _RRNXT
    }

_STF_SC_PAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> SCEF -> a -> a -> ContractStatePoly a b
_STF_SC_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _SCEF o_rf_SCMO _SCIED =
    let
        st' = _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL

        nsc' = case _SCEF of
            SE_00M -> nsc
            SE_I00 -> nsc
            _      -> (o_rf_SCMO - _SCIED) / _SCIED

        isc' = case _SCEF of
            SE_0N0 -> isc
            SE_00M -> isc
            SE_0NM -> isc
            _      -> (o_rf_SCMO - _SCIED) / _SCIED
    in st' {nsc = nsc', isc = isc'}

_STF_CE_PAM :: ActusNum a => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_CE_PAM = _STF_AD_PAM

-- Linear Amortiser
_STF_AD_LAM :: ActusNum a => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_AD_LAM = _STF_AD_PAM

_STF_IED_LAM :: (RoleSignOps a1, ActusNum a1, DateOps a2 a1, ActusOps a1) => ContractStatePoly a1 a2 -> a2 -> a1 -> Maybe a1 -> Maybe a2 -> CR -> Maybe a1 -> a1 -> Maybe IPCB -> Maybe a1 -> ContractStatePoly a1 a2
_STF_IED_LAM st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT _IPCB _IPCBA =
    let
        nt'                         = _r _CNTRL * _NT
        ipnr'                       = fromJust _IPNR

        ipac' | isJust _IPAC        = fromJust _IPAC
              | isJust _IPANX       = _lt (fromJust _IPANX) t * y_ipanx_t * nt' * ipnr'
              | otherwise           = _zero

        ipcb' | fromJust _IPCB == IPCB_NT = _r _CNTRL * _NT
              | otherwise                 = _r _CNTRL * fromJust _IPCBA
    in st { nt = nt', ipnr = ipnr', ipac = ipac', ipcb = ipcb', sd = t }

_STF_PR_LAM :: (ActusNum a, RoleSignOps a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe IPCB -> ContractStatePoly a b
_STF_PR_LAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _IPCB =
    let
        nt' = nt - _r _CNTRL * prnxt

        fac' = case _FEB of
            Just FEB_N -> fac + y_sd_t * nt * _FER
            _          -> y_tfpminus_t / y_tfpminus_tfpplus * _r _CNTRL * _FER

        ipcb' = case fromJust _IPCB of
            IPCB_NT -> nt'
            _       -> ipcb

     in st {nt = nt', fac = fac', ipcb = ipcb', sd = t}

_STF_MD_LAM :: ActusOps a => ContractStatePoly a b -> b -> ContractStatePoly a b
_STF_MD_LAM st t = st {
    nt = _zero,
    ipac = _zero,
    feac = _zero,
    ipcb = _zero,
    sd = t
}

_STF_PP_LAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe IPCB -> ContractStatePoly a b
_STF_PP_LAM st@ContractStatePoly{..} t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _IPCB =
    let
        st' = _STF_PY_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
        nt' = nt - pp_payoff
        ipcb' = case fromJust _IPCB of
            IPCB_NT -> nt'
            _       -> ipcb
    in st' {nt = nt', ipcb = ipcb'}

_STF_PY_LAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_PY_LAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL =
    let
        ipac' = ipac + y_sd_t * ipnr * ipcb

        fac' = case _FEB of
            Just FEB_N -> fac + y_sd_t * nt * _FER
            _          -> y_tfpminus_t / y_tfpminus_tfpplus * _r _CNTRL * _FER

    in st {ipac = ipac', fac = fac', sd = t}

_STF_FP_LAM :: (ActusNum a, ActusOps a) => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_FP_LAM st@ContractStatePoly{..} t y_sd_t = st {
    ipac = ipac + y_sd_t * ipnr * ipcb,
    fac = _zero,
    sd = t
}

_STF_PRD_LAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_PRD_LAM = _STF_PY_LAM

_STF_TD_LAM :: ActusOps a => ContractStatePoly a b -> b -> ContractStatePoly a b
_STF_TD_LAM = _STF_TD_PAM

_STF_IP_LAM :: (ActusOps a, RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_IP_LAM = _STF_IP_PAM

_STF_IPCI_LAM :: (ActusOps a, RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe IPCB -> ContractStatePoly a b
_STF_IPCI_LAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _IPCB =
    let
        st' = _STF_IP_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
        nt' = nt + ipac + y_sd_t * ipnr * ipcb
        ipcb' = case fromJust _IPCB of
            IPCB_NT -> nt'
            _       -> ipcb
    in st' {nt = nt', ipcb = ipcb'}

_STF_IPCB_LAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_IPCB_LAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL =
    let st' = _STF_PRD_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
    in st' { ipcb = nt }

_STF_RR_LAM :: (ActusOps a, RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> a -> a -> a -> a -> a -> a -> a -> ContractStatePoly a b
_STF_RR_LAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRLF _RRLC _RRPC _RRPF _RRMLT _RRSP o_rf_RRMO =
    let
        st' = _STF_PRD_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL

        delta_r = _min (_max (o_rf_RRMO * _RRMLT + _RRSP - ipnr) _RRPF) _RRPC

        ipnr' = _min (_max (ipnr + delta_r) _RRLF) _RRLC
    in st' {ipnr = ipnr'}

_STF_RRF_LAM :: (ActusOps a, RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe a -> ContractStatePoly a b
_STF_RRF_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRNXT =
    let st' = _STF_PRD_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
    in st' { ipnr = fromMaybe _zero _RRNXT }

_STF_SC_LAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> SCEF -> a -> a -> ContractStatePoly a b
_STF_SC_LAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _SCEF o_rf_SCMO _SCIED =
    let
        st' = _STF_PY_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL

        nsc' = case _SCEF of
            SE_00M -> nsc
            SE_I00 -> nsc
            _      -> (o_rf_SCMO - _SCIED) / _SCIED

        isc' = case _SCEF of
            SE_0N0 -> isc
            SE_00M -> isc
            SE_0NM -> isc
            _      -> (o_rf_SCMO - _SCIED) / _SCIED
    in st' {nsc = nsc', isc = isc'}

_STF_CE_LAM :: ActusNum a => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_CE_LAM = _STF_AD_PAM

-- Negative Amortizer
_STF_AD_NAM :: ActusNum a => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_AD_NAM = _STF_AD_PAM

_STF_IED_NAM :: (RoleSignOps a1, ActusNum a1, DateOps a2 a1, ActusOps a1) => ContractStatePoly a1 a2 -> a2 -> a1 -> Maybe a1 -> Maybe a2 -> CR -> Maybe a1 -> a1 -> Maybe IPCB -> Maybe a1 -> ContractStatePoly a1 a2
_STF_IED_NAM = _STF_IED_LAM

_STF_PR_NAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe IPCB -> ContractStatePoly a b
_STF_PR_NAM st@ContractStatePoly{..} t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _IPCB =
    let st'@ContractStatePoly{ ipac = ipac' } = _STF_PP_LAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _IPCB
        nt' = nt - prnxt - ipac'
    in st' { nt = nt' }

_STF_MD_NAM :: ActusOps a => ContractStatePoly a b -> b -> ContractStatePoly a b
_STF_MD_NAM = _STF_MD_LAM

_STF_PP_NAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe IPCB -> ContractStatePoly a b
_STF_PP_NAM = _STF_PP_LAM

_STF_PY_NAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_PY_NAM = _STF_PY_LAM

_STF_FP_NAM :: (ActusNum a, ActusOps a) => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_FP_NAM = _STF_FP_LAM

_STF_PRD_NAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_PRD_NAM = _STF_PRD_LAM

_STF_TD_NAM :: ActusOps a => ContractStatePoly a b -> b -> ContractStatePoly a b
_STF_TD_NAM = _STF_TD_PAM

_STF_IP_NAM :: (ActusOps a, RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_IP_NAM = _STF_IP_PAM

_STF_IPCI_NAM :: (ActusOps a, RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe IPCB -> ContractStatePoly a b
_STF_IPCI_NAM = _STF_IPCI_LAM

_STF_IPCB_NAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_IPCB_NAM = _STF_IPCB_LAM

_STF_RR_NAM :: (ActusOps a, RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> a -> a -> a -> a -> a -> a -> a -> ContractStatePoly a b
_STF_RR_NAM = _STF_RR_LAM

_STF_RRF_NAM :: (ActusOps a, RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe a -> ContractStatePoly a b
_STF_RRF_NAM = _STF_RRF_LAM

_STF_SC_NAM :: (RoleSignOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> SCEF -> a -> a -> ContractStatePoly a b
_STF_SC_NAM = _STF_SC_LAM

_STF_CE_NAM :: ActusNum a => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_CE_NAM = _STF_AD_PAM
