{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Model.INIT.StateInitialization where

import           Data.Maybe                                                 (fromMaybe)
import           Data.Time                                                  (Day)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents          (EventType (FP, IP))
import           Language.Marlowe.ACTUS.Definitions.ContractState           (ContractState)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms           (ContractTerms (..),
                                                                             ContractType (LAM, PAM), ScheduleConfig)
import           Language.Marlowe.ACTUS.Definitions.Schedule                (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (_INIT_PAM)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule        (schedule)
import           Language.Marlowe.ACTUS.Model.Utility.DateShift             (applyBDCWithCfg)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator     (inf, sup)


shift :: ScheduleConfig -> Day -> ShiftedDay
shift = applyBDCWithCfg

inititializeState :: ContractTerms -> ContractState
inititializeState terms@ContractTerms {..} =
    let t0         = ct_SD
        fpSchedule = fromMaybe [shift scfg t0] $ schedule FP terms
        ipSchedule = fromMaybe [shift scfg t0] $ schedule IP terms
        tminus     = calculationDay $ sup ipSchedule t0
        tfp_minus  = calculationDay $ sup fpSchedule t0
        tfp_plus   = calculationDay $ inf fpSchedule t0
    in  case contractType of
        PAM -> _INIT_PAM t0 tminus tfp_minus tfp_plus ct_MD ct_IED ct_IPNR ct_CNTRL ct_NT ct_IPAC ct_DCC (Just ct_FER) ct_FEAC ct_FEB ct_SCEF ct_SCIXSD ct_PRF
        LAM -> undefined
