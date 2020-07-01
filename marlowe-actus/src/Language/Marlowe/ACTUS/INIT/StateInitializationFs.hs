{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.INIT.StateInitializationFs where

import Language.Marlowe
import Language.Marlowe.ACTUS.ContractTerms
    ( ContractTerms(..), ContractType(LAM, PAM), ScheduleConfig )
import Language.Marlowe.ACTUS.ContractState ( ContractState )
import Language.Marlowe.ACTUS.BusinessEvents ( EventType(IP, FP) )
import Language.Marlowe.ACTUS.INIT.StateInitializationModel
    ( _INIT_PAM )
import Language.Marlowe.ACTUS.SCHED.ContractSchedule ( schedule )
import Language.Marlowe.ACTUS.Utility.ScheduleGenerator
    ( sup, inf )
import Language.Marlowe.ACTUS.Schedule
    ( ShiftedDay(calculationDay) )
import Data.Maybe ( fromMaybe )
import Data.Time ( Day )
import Language.Marlowe.ACTUS.Utility.DateShift ( applyBDCWithCfg )
import Language.Marlowe.ACTUS.MarloweCompat


shift :: ScheduleConfig -> Day -> ShiftedDay
shift = applyBDCWithCfg

inititializeStateFs :: ContractTerms -> Contract -> Contract
inititializeStateFs terms@ContractTerms {..} continue =
    let t0         = _SD
        fpSchedule = fromMaybe [shift scfg t0] $ schedule FP terms
        ipSchedule = fromMaybe [shift scfg t0] $ schedule IP terms
        tminus     = calculationDay $ sup ipSchedule t0
        tfp_minus  = calculationDay $ sup fpSchedule t0
        tfp_plus   = calculationDay $ inf fpSchedule t0
        initialState =  case contractType of
            PAM -> _INIT_PAM t0 tminus tfp_minus tfp_plus _MD _IED _IPNR _CNTRL _NT _IPAC _DCC (Just _FER) _FEAC _FEB _SCEF _SCIXSD _PRF
            LAM -> undefined
    in stateInitialisation initialState continue
