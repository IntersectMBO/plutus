module Language.Marlowe.ACTUS.HP.INIT.PAM where

import Language.Marlowe.ACTUS.HP.ContractState
import Language.Marlowe.ACTUS.HP.Utility.ContractRoleSign
import Language.Marlowe.ACTUS.HP.Utility.YearFraction
import Language.Marlowe.ACTUS.HP.ContractTerms
import Data.Time
import Data.Maybe

r = contractRoleSign
y = yearFraction

scef_xNx SE_0N0 = True -- List.elem ...
scef_xNx SE_0NM = True
scef_xNx SE_IN0 = True
scef_xNx SE_INM = True
scef_xNx _      = False
scef_Ixx SE_IN0 = True
scef_Ixx SE_INM = True
scef_Ixx SE_I00 = True
scef_Ixx SE_I0M = True
scef_Ixx _      = False

--t0 == SD
_INIT_PAM t0 tminus tfp_minus tfp_plus _MD _IED _IPNR _CNTRL _NT _IPAC _DCC _FER _FEAC _FEB _SCEF _SCIXSD _PRF = 
    let 
        tmd   = _MD
        nt    = if _IED > t0             then 0.0 
                else                          (r _CNTRL) * _NT
        ipnr  = if _IED > t0             then 0.0 
                else                          fromMaybe 0.0 _IPNR
        ipac  = if      isNothing _IPNR  then 0.0 
                else if isJust _IPAC     then fromJust _IPAC
                else                          (y _DCC tminus t0 _MD) * nt * ipnr
        fac   = if      isNothing _FER   then 0.0
                else if isJust _FEAC     then fromJust _FEAC
                else if _FEB == FEB_N     then (y _DCC tfp_minus t0 _MD) * nt * fromJust _FER
                else                          ((y _DCC tfp_minus t0 _MD) / (y _DCC tfp_minus tfp_plus _MD)) * fromJust _FER
        nsc   = if scef_xNx _SCEF        then _SCIXSD
                                         else 1.0
        isc   = if scef_Ixx _SCEF        then _SCIXSD
                                         else 1.0
        prf   = _PRF
        sd    = t0
    in ContractState { tmd = tmd, nt = nt, ipnr = ipnr, ipac = ipac, fac = fac, nsc = nsc, isc = isc, prf = prf, sd = sd }
    