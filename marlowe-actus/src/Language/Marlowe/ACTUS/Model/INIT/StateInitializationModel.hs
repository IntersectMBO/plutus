{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel where

import           Data.List                                              as L (filter, head, last)
import           Data.Maybe                                             (fromJust, fromMaybe, isJust, isNothing)
import           Language.Marlowe.ACTUS.Definitions.ContractState       (ContractStatePoly (ContractStatePoly, feac, ipac, ipcb, ipnr, isc, nsc, nt, prf, prnxt, sd, tmd))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (ContractTerms (..), Cycle (..), FEB (FEB_N),
                                                                         IPCB (IPCB_NT),
                                                                         SCEF (SE_0N0, SE_0NM, SE_I00, SE_I0M, SE_IN0, SE_INM),
                                                                         ScheduleConfig (..), n)
import           Language.Marlowe.ACTUS.Definitions.Schedule            (ShiftedDay (..))
import           Language.Marlowe.ACTUS.Model.Utility.ContractRoleSign  (contractRoleSign)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (applyEOMC,
                                                                         generateRecurrentScheduleWithCorrections,
                                                                         minusCycle, moveToEndOfMonth, plusCycle)
import           Language.Marlowe.ACTUS.Model.Utility.YearFraction      (yearFraction)


_S = generateRecurrentScheduleWithCorrections
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



_INIT_PAM t0 tminus tfp_minus tfp_plus
  ContractTerms{
      ct_CNTRL  = _CNTRL
    , ct_IED    = _IED
    , ct_DCC    = _DCC
    , ct_PRF    = _PRF
    , ct_FEAC   = _FEAC
    , ct_FEB    = _FEB
    , ct_FER    = _FER
    , ct_IPAC   = _IPAC
    , ct_IPNR   = _IPNR
    , ct_NT     = _NT
    , ct_MD     = _MD
    , ct_SCEF   = _SCEF
    , ct_SCNT   = _SCNT
    , ct_SCIP   = _SCIP
  } =
    let
        _IED'   = fromJust _IED
        _DCC'   = fromJust _DCC
        _PRF'   = fromJust _PRF
        _SCEF'  = fromJust _SCEF
        _SCNT'  = fromJust _SCNT
        _SCIP'  = fromJust _SCIP

        tmd                                     = fromJust _MD
        nt
                | _IED' > t0                    = 0.0
                | otherwise                     = r _CNTRL * fromJust _NT
        ipnr
                | _IED' > t0                    = 0.0
                | otherwise                     = fromMaybe 0.0 _IPNR
        ipac
                | isNothing _IPNR               = 0.0
                | isJust _IPAC                  = r _CNTRL * fromJust _IPAC
                | otherwise                     = (y _DCC' tminus t0 _MD) * nt * ipnr
        feac
                | isNothing _FER                = 0.0
                | isJust _FEAC                  = fromJust _FEAC
                | fromJust _FEB == FEB_N        = y _DCC' tfp_minus t0 _MD * nt * fromJust _FER
                | otherwise                     = (y _DCC' tfp_minus t0 _MD / y _DCC' tfp_minus tfp_plus _MD) * fromJust _FER
        nsc
                | scef_xNx _SCEF'               = _SCNT'
                | otherwise                     = 1.0
        isc
                | scef_Ixx _SCEF'               = _SCIP'
                | otherwise                     = 1.0
        prf                                     = _PRF'
        sd                                      = t0
    in ContractStatePoly { prnxt = 0.0, ipcb = 0.0, tmd = tmd, nt = nt, ipnr = ipnr, ipac = ipac, feac = feac, nsc = nsc, isc = isc, prf = prf, sd = sd }

_INIT_LAM t0 tminus tpr_minus tfp_minus tfp_plus
  terms@ContractTerms{
      ct_CNTRL = _CNTRL
    , ct_IED   = _IED
    , ct_DCC   = _DCC
    , ct_IPCL  = _IPCL
    , ct_IPCB  = _IPCB
    , ct_IPCBA = _IPCBA
    , ct_NT    = _NT
    , ct_MD    = _MD
    , ct_PRANX = _PRANX
    , ct_PRCL  = _PRCL
    , ct_PRNXT = _PRNXT
    , ct_SD    = _SD
    , scfg     = scfg
  } =
    let
        _IED' = fromJust _IED
        _DCC' = fromJust _DCC

        -- TMD
        -- maybeTMinus
        --             | isJust _PRANX && ((fromJust _PRANX) >= t0) = _PRANX
        --             | (_IED' `plusCycle` fromJust _PRCL) >= t0 = Just $ _IED' `plusCycle` fromJust _PRCL
        --             | otherwise                           = Just tpr_minus
        -- tmd
        --         | isJust _MD = fromJust _MD
        --         | otherwise = fromJust maybeTMinus `plusCycle` (fromJust _PRCL) { n = ((ceiling ((fromJust _NT) / (fromJust _PRNXT))) * (n (fromJust _PRCL))) }

        -- TMD
        tmd
          | isJust _MD = fromJust _MD
          | otherwise =
            let
              (lastEvent, remainingPeriods) =
                if isJust _PRANX && fromJust _PRANX < _SD then
                  let
                    previousEvents   = (\s -> _S s (fromJust _PRCL) _SD scfg ) <$> _PRANX
                    previousEvents'  = L.filter(\ShiftedDay{ calculationDay = calculationDay } -> calculationDay > (minusCycle _SD (fromJust _IPCL))) (fromMaybe [] previousEvents)
                    previousEvents'' = L.filter(\ShiftedDay{ calculationDay = calculationDay } -> calculationDay == _SD) previousEvents'
                    ShiftedDay{ calculationDay = lastEventCalcDay } = L.head previousEvents''
                  in
                    (lastEventCalcDay, (fromJust _NT) / (fromJust _PRNXT))
                else
                  -- TODO: check applicability for PRANX
                  (fromJust _PRANX, (fromJust _NT) / (fromJust _PRNXT) - 1)
              cycle@Cycle{ n = n } = fromJust _PRCL
              maturity = plusCycle lastEvent cycle{ n = n * (round remainingPeriods) :: Integer}
            in
              applyEOMC lastEvent cycle (fromJust (eomc scfg)) maturity


        pam_init = _INIT_PAM t0 tminus tfp_minus tfp_plus terms

        -- PRNXT
        -- s
        --         | isJust _PRANX && ((fromJust _PRANX) > t0) = fromJust _PRANX
        --         | isNothing _PRANX && ((_IED' `plusCycle` fromJust _PRCL) > t0) = _IED' `plusCycle` fromJust _PRCL
        --         | otherwise = tpr_minus
        prnxt
                | isJust _PRNXT                 = fromJust _PRNXT
                -- ACTUS implementation
                -- | otherwise                     = (fromJust _NT) * (1.0 / (fromIntegral $ ((ceiling (y _DCC' s tmd (Just tmd) / y _DCC' s (s `plusCycle` fromJust _PRCL) (Just tmd))) :: Integer)))

                -- Java implementation
                | otherwise = (fromJust _NT) / (fromIntegral (length $ fromJust ((\s -> _S s (fromJust _PRCL){ includeEndDay = True } tmd scfg ) <$> _PRANX)))
        -- IPCB
        ipcb
                | t0 < _IED'                    = 0.0
                | fromJust _IPCB == IPCB_NT     = r _CNTRL * fromJust _NT
                | otherwise                     = r _CNTRL * fromJust _IPCBA
    -- All is same as PAM except PRNXT, IPCB, and TMD
    in pam_init { prnxt = prnxt, ipcb = ipcb, tmd = tmd }

_INIT_NAM t0 tminus tpr_minus tfp_minus tfp_plus
  terms@ContractTerms{
      ct_CNTRL = _CNTRL
    , ct_IED   = _IED
    , ct_DCC   = _DCC
    , ct_IPCB  = _IPCB
    , ct_IPCBA = _IPCBA
    , ct_IPNR  = _IPNR
    , ct_NT    = _NT
    , ct_MD    = _MD
    , ct_PRANX = _PRANX
    , ct_PRCL  = _PRCL
    , ct_PRNXT = _PRNXT
    , ct_SD    = _SD
    , scfg     = scfg
  } =
    let
        _IED'   = fromJust _IED
        _DCC'   = fromJust _DCC
        _PRNXT' = fromJust _PRNXT

        -- TMD
        maybeTMinus
                    | isJust _PRANX && ((fromJust _PRANX) >= t0) = _PRANX
                    | (_IED' `plusCycle` fromJust _PRCL) >= t0 = Just $ _IED' `plusCycle` fromJust _PRCL
                    | otherwise                           = Just tpr_minus
        tmd
                | isJust _MD = fromJust _MD
                | otherwise =
                  let
                    lastEvent =
                      if isJust _PRANX && (fromJust _PRANX) >= _SD then
                        fromJust _PRANX
                      else
                        if _IED' `plusCycle` (fromJust _PRCL) >= _SD then
                          _IED' `plusCycle` (fromJust _PRCL)
                        else
                          let previousEvents  = (\s -> _S s (fromJust _PRCL) _SD scfg ) <$> _PRANX
                              previousEvents'  = L.filter(\ShiftedDay{ calculationDay = calculationDay } -> calculationDay >= _SD ) (fromMaybe [] previousEvents)
                              previousEvents'' = L.filter(\ShiftedDay{ calculationDay = calculationDay } -> calculationDay == _SD) previousEvents'
                              ShiftedDay{ calculationDay = lastEventCalcDay } = L.head previousEvents''
                          in
                              lastEventCalcDay
                    yLastEventPlusPRCL = (y _DCC' lastEvent (lastEvent `plusCycle` (fromJust _PRCL)) _MD)
                    redemptionPerCycle = _PRNXT' - (yLastEventPlusPRCL * (fromJust _IPNR) * (fromJust _NT))
                    remainingPeriods = (ceiling ((fromJust _NT) / redemptionPerCycle)) - 1
                    cycle@Cycle{ n = n } = fromJust _PRCL
                    maturity = plusCycle lastEvent cycle{ n = n * remainingPeriods}
                  in
                    applyEOMC lastEvent cycle (fromJust (eomc scfg)) maturity
                -- | otherwise = fromJust maybeTMinus `plusCycle` (fromJust _PRCL) { n = ceiling((fromJust _NT) / (_PRNXT' - (fromJust _NT)  * (y _DCC' tminus (tminus `plusCycle` fromJust _PRCL) _MD) * fromJust _IPNR))}

        pam_init = _INIT_PAM t0 tminus tfp_minus tfp_plus terms

        -- PRNXT
        prnxt = _PRNXT'

        -- IPCB
        ipcb
                | t0 < _IED'                    = 0.0
                | fromJust _IPCB == IPCB_NT     = r _CNTRL * fromJust _NT
                | otherwise                     = r _CNTRL * fromJust _IPCBA
    -- All is same as PAM except PRNXT and TMD, IPCB same as LAM
    in pam_init { prnxt = prnxt, ipcb = ipcb, tmd = tmd }
