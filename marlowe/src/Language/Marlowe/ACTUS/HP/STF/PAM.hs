{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.HP.STF.PAM where

import Language.Marlowe.ACTUS.HP.Utility.ContractRoleSign
import Language.Marlowe.ACTUS.HP.Utility.YearFraction
import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.ContractState
import Data.Time
import Data.Maybe

r = contractRoleSign
y = yearFraction

_STF_AD_PAM st@ContractState{..} _DCC _MD = ContractState {
    ipac = ipac + (y _DCC sd t _MD) * ipnr * nt,
    sd = t 
}

_STF_IED_PAM st@ContractState{..} _DCC _MD _IPNR _IPANX _CNTRL _IPAC _NT = 
    let 
        yy = (y _DCC (fromJust _IPANX) t _MD)
        nt' = (r _CNTRL) * _NT
        ipnr' = if (isNothing _IPNR) then 0.0 else (fromJust _IPNR)
        ipac' = if (isJust _IPAC) then (fromJust _IPAC)
                else if (isJust _IPANX && (fromJust _IPANX) < t) then yy * nt' * ipnr'
                else 0.0
    in ContractState { nt = nt', ipnr = ipnr', ipac = ipac', sd = t }

_STF_MD_PAM st@ContractState{..} = ContractState {
    nt = 0.0,
    ipac = 0.0,
    feac = 0.0,
    sd = t
}

_STF_PP_PAM st@ContractState{..} pp_payoff _DCC _MD tfp_minus tfp_plus _FEB _FER _CNTRL =
    let
        ipac' = ipac + (y _DCC sd t _MD) * ipnr * nt
        fac' = case _FEB of 
            FEB_N -> fac + (y _DCC sd t _MD) * nt * _FER
            otherwise -> ((y _DCC tfp_minus t _MD) / (y _DCC tfp_minus tfp_plus _MD)) * (r _CNTRL) * _FER
        nt' = nt - pp_payoff
    in ContractState {ipac = ipac', fac = fac', nt = nt', sd = t}

_STF_PY_PAM st@ContractState{..} = st

_STF_FP_PAM st@ContractState{..} = st

_STF_PRD_PAM st@ContractState{..} = st

_STF_TD_PAM st@ContractState{..} = ContractState {
    nt = 0.0,
    ipac = 0.0,
    fac = 0.0,
    ipnr = 0.0,
    sd = t
}

_STF_IP_PAM st@ContractState{..} = st

_STF_IPCI_PAM st@ContractState{..} = st

_STF_RR_PAM st@ContractState{..} = st

_STF_RRF_PAM st@ContractState{..} = st

_STF_SC_PAM st@ContractState{..} = st

_STF_CE_PAM st@ContractState{..} = st