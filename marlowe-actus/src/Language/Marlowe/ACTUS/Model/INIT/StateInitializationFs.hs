{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Model.INIT.StateInitializationFs where

import           Data.Maybe                                                 (fromMaybe)
import           Language.Marlowe
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents          (EventType (FP, IP))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms           (ContractTerms (..),
                                                                             ContractType (LAM, PAM))
import           Language.Marlowe.ACTUS.Definitions.Schedule                (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.MarloweCompat                       (stateInitialisation)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (_INIT_PAM)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule        (schedule)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator     (inf, sup)

inititializeStateFs :: ContractTerms -> Contract -> Contract
inititializeStateFs terms@ContractTerms {..} continue =
    let t0                 = ct_SD
        fpSchedule         = schedule FP terms
        tfp_minus          = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< fpSchedule)
        tfp_plus           = fromMaybe t0 $ calculationDay <$> ((\sc -> inf sc t0) =<< fpSchedule)
        ipSchedule         = schedule IP terms
        tminus             = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< ipSchedule)
        initialState =  case contractType of
            PAM -> _INIT_PAM t0 tminus tfp_minus tfp_plus ct_MD ct_IED ct_IPNR ct_CNTRL ct_NT ct_IPAC ct_DCC (Just ct_FER) ct_FEAC ct_FEB ct_SCEF ct_SCIXSD ct_PRF
            LAM -> undefined
    in stateInitialisation initialState continue
