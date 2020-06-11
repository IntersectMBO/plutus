{-# OPTIONS_GHC -fno-warn-missing-signatures #-} 
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Language.Marlowe.ACTUS.INIT.StateInitializationSpec where

import Language.Marlowe.ACTUS.ContractState
    ( ContractStatePoly(ContractStatePoly, prnxt, ipcb, tmd, nt, ipnr,
                        ipac, fac, feac, nsc, isc, prf, sd) )
import Language.Marlowe.ACTUS.Utility.ContractRoleSign
    ( contractRoleSign )
import Language.Marlowe.ACTUS.Utility.YearFraction ( yearFraction )
import Language.Marlowe.ACTUS.ContractTerms
    ( SCEF(SE_I0M, SE_0N0, SE_0NM, SE_IN0, SE_INM, SE_I00),
      FEB(FEB_N) )
import Data.Maybe ( fromJust, fromMaybe, isJust, isNothing )


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
        tmd                                     = _MD
        nt     
                | _IED > t0                     = 0.0 
                | otherwise                     = r _CNTRL * _NT
        ipnr    
                | _IED > t0                     = 0.0 
                | otherwise                     = fromMaybe 0.0 _IPNR
        ipac    
                | isNothing _IPNR               = 0.0 
                | isJust _IPAC                  = fromJust _IPAC
                | otherwise                     = y _DCC tminus t0 _MD * nt * ipnr
        fac
                | isNothing _FER                = 0.0
                | isJust _FEAC                  = fromJust _FEAC
                | _FEB == FEB_N                  = y _DCC tfp_minus t0 _MD * nt * fromJust _FER
                | otherwise                     = (y _DCC tfp_minus t0 _MD / y _DCC tfp_minus tfp_plus _MD) * fromJust _FER        
        feac
                | isNothing _FER                = 0.0
                | isJust _FEAC                  = fromJust _FEAC
                | _FEB == FEB_N                  = y _DCC tfp_minus t0 _MD * nt * fromJust _FER
                | otherwise                     = (y _DCC tfp_minus t0 _MD / y _DCC tfp_minus tfp_plus _MD) * fromJust _FER
        nsc     
                | scef_xNx _SCEF                = _SCIXSD
                | otherwise                     = 1.0
        isc     
                | scef_Ixx _SCEF                = _SCIXSD
                | otherwise                     = 1.0
        prf                                     = _PRF
        sd                                      = t0
    in ContractStatePoly { prnxt = 0.0, ipcb = 0.0, tmd = tmd, nt = nt, ipnr = ipnr, ipac = ipac, fac = fac, feac = feac, nsc = nsc, isc = isc, prf = prf, sd = sd }
    