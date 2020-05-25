{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.INIT.StateInitialization where

import Language.Marlowe.ACTUS.ContractTerms
import Language.Marlowe.ACTUS.ContractState
import Language.Marlowe.ACTUS.BusinessEvents
import Language.Marlowe.ACTUS.INIT.StateInitializationSpec
import Language.Marlowe.ACTUS.SCHED.ContractSchedule
import Language.Marlowe.ACTUS.Utility.ScheduleGenerator
import Language.Marlowe.ACTUS.Schedule
import Data.Maybe
import Language.Marlowe.ACTUS.Utility.DateShift

shift = applyBDCWithCfg

inititializeState :: ContractTerms -> ContractState
inititializeState terms = 
    case terms of
        PamContractTerms{..} -> 
            let 
                t0 = _SD
                fpSchedule = fromMaybe [shift scfg t0] $ schedule FP terms
                ipSchedule = fromMaybe [shift scfg t0] $ schedule IP terms
                tminus = calculationDay $ sup ipSchedule t0
                tfp_minus = calculationDay $ sup fpSchedule t0
                tfp_plus = calculationDay $ inf fpSchedule t0
            in _INIT_PAM t0 tminus tfp_minus tfp_plus 
                    _MD _IED _IPNR _CNTRL _NT _IPAC _DCC (Just _FER) _FEAC _FEB _SCEF _SCIXSD _PRF
        LamContractTerms{..} -> undefined