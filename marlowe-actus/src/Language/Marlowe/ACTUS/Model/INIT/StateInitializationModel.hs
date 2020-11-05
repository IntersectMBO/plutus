{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel where

import           Data.Maybe                                            (fromJust, fromMaybe, isJust, isNothing)
import           Language.Marlowe.ACTUS.Definitions.ContractState      (ContractStatePoly (ContractStatePoly, fac, feac, ipac, ipcb, ipnr, isc, nsc, nt, prf, prnxt, sd, tmd))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms      (FEB (FEB_N), SCEF (SE_0N0, SE_0NM, SE_I00, SE_I0M, SE_IN0, SE_INM), IPCB (IPCB_NT), n)
import           Language.Marlowe.ACTUS.Model.Utility.ContractRoleSign (contractRoleSign)
import           Language.Marlowe.ACTUS.Model.Utility.YearFraction     (yearFraction)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (plusCycle)


r = contractRoleSign
y = yearFraction

scef_xNx SE_0N0 = True
scef_xNx SE_0NM = True
scef_xNx SE_IN0 = True
scef_xNx SE_INM = True
scef_xNx _      = False
scef_Ixx SE_IN0 = True
scef_Ixx SE_INM = True
scef_Ixx SE_I00 = True
scef_Ixx SE_I0M = True
scef_Ixx _      = False



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

_INIT_LAM t0 tminus tpr_minus tfp_minus tfp_plus _MD _IED _IPNR _CNTRL _NT _IPAC _DCC _FER _FEAC _FEB _SCEF _SCIXSD _PRF _PRCL _PRANX _PRNXT _IPCB _IPCBA =
    let
        -- Tmd
        maybeTMinus 
                    | isJust _PRANX && ((fromJust _PRANX) >= t0) = _PRANX
                    | (_IED `plusCycle` fromJust _PRCL) >= t0 = Just $ _IED `plusCycle` fromJust _PRCL
                    | otherwise                           = Just tpr_minus
        tmd
                | isJust _MD = fromJust _MD
                | otherwise = fromJust maybeTMinus `plusCycle` (fromJust _PRCL) { n = ((ceiling (_NT / (fromJust _PRNXT))) * (n (fromJust _PRCL))) }

        pam_init = _INIT_PAM t0 tminus tfp_minus tfp_plus tmd _IED _IPNR _CNTRL _NT _IPAC _DCC _FER _FEAC _FEB _SCEF _SCIXSD _PRF

        -- Same as PAM
        _nt = nt pam_init

        -- Same as PAM
        _ipnr = ipnr pam_init

        -- Same as PAM
        _ipac = ipac pam_init

        -- Same as PAM
        _fac = fac pam_init

        -- Same as PAM
        _feac = feac pam_init

        -- Same as PAM
        _nsc = nsc pam_init

        -- Same as PAM
        _isc = isc pam_init

        -- Same as PAM
        _prf = prf pam_init
        
        -- Same as PAM
        _sd = sd pam_init

        -- PRNXT
        s
                | isJust _PRANX && ((fromJust _PRANX) > t0) = fromJust _PRANX
                | isNothing _PRANX && ((_IED `plusCycle` (fromJust _PRCL)) > t0) = _IED `plusCycle` (fromJust _PRCL)
                | otherwise = tpr_minus
        prnxt
                | isJust _PRNXT                 = fromJust _PRNXT
                | otherwise                     = _NT * (1.0 / (fromIntegral $ ((ceiling (y _DCC s tmd tmd / y _DCC s (s `plusCycle` (fromJust _PRCL)) tmd)) :: Integer)))

        -- IPCB
        ipcb
                | t0 < _IED                    = 0.0
                | (fromJust _IPCB) == IPCB_NT              = r _CNTRL * _NT
                | otherwise                     = r _CNTRL * (fromJust _IPCBA)
    in ContractStatePoly { prnxt = prnxt, ipcb = ipcb, tmd = tmd, nt = _nt, ipnr = _ipnr, ipac = _ipac, fac = _fac, feac = _feac, nsc = _nsc, isc = _isc, prf = _prf, sd = _sd }