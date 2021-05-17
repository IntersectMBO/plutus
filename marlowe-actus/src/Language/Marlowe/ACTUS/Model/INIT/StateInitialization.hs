{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Model.INIT.StateInitialization where

import           Data.Maybe                                                 (fromMaybe)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents          (EventType (FP, IP, PR))
import           Language.Marlowe.ACTUS.Definitions.ContractState           (ContractState)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms           (CT (LAM, NAM, PAM), ContractTerms (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule                (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (_INIT_LAM, _INIT_NAM, _INIT_PAM)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule        (schedule)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator     (inf, sup)


inititializeState :: ContractTerms -> ContractState
inititializeState terms@ContractTerms {..} =
    let t0         = ct_SD
        -- PAM
        fpSchedule         = schedule FP terms
        tfp_minus          = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< fpSchedule)
        tfp_plus           = fromMaybe t0 $ calculationDay <$> ((\sc -> inf sc t0) =<< fpSchedule)
        ipSchedule         = schedule IP terms
        tminus             = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< ipSchedule)
        -- LAM, NAM
        prSchedule         = schedule PR terms
        tpr_minus          = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< prSchedule)
    in  case contractType of
        PAM -> _INIT_PAM t0 tminus tfp_minus tfp_plus terms
        LAM -> _INIT_LAM t0 tminus tpr_minus tfp_minus tfp_plus terms
        NAM -> _INIT_NAM t0 tminus tpr_minus tfp_minus tfp_plus terms
