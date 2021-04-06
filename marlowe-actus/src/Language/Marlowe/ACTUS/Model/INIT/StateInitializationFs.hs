{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Model.INIT.StateInitializationFs where

import           Data.Maybe                                                 (fromJust, fromMaybe)
import           Language.Marlowe
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents          (EventType (FP, IP, PR))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms           (ContractTerms (..),
                                                                             ContractType (LAM, NAM, PAM))
import           Language.Marlowe.ACTUS.Definitions.Schedule                (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.MarloweCompat                       (stateInitialisation)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (_INIT_LAM, _INIT_NAM, _INIT_PAM)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule        (schedule)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator     (inf, sup)

inititializeStateFs :: ContractTerms -> Contract -> Contract
inititializeStateFs terms@ContractTerms {..} continue =
    let t0                 = ct_SD
        -- PAM
        fpSchedule         = schedule FP terms
        tfp_minus          = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< fpSchedule)
        tfp_plus           = fromMaybe t0 $ calculationDay <$> ((\sc -> inf sc t0) =<< fpSchedule)
        ipSchedule         = schedule IP terms
        tminus             = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< ipSchedule)
        -- LAM, NAM
        prSchedule         = schedule PR terms
        tpr_minus          = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< prSchedule)
        initialState =  case fromJust contractType of
            PAM -> _INIT_PAM t0 tminus tfp_minus tfp_plus ct_MD ct_IED ct_IPNR ct_CNTRL (fromJust ct_NT) ct_IPAC ct_DCC (Just ct_FER) ct_FEAC ct_FEB ct_SCEF ct_SCIXSD ct_PRF
            LAM -> _INIT_LAM t0 tminus tpr_minus tfp_minus tfp_plus ct_MD ct_IED ct_IPNR ct_CNTRL (fromJust ct_NT) ct_IPAC ct_DCC (Just ct_FER) ct_FEAC ct_FEB ct_SCEF ct_SCIXSD ct_PRF ct_PRCL ct_PRANX ct_PRNXT ct_IPCB ct_IPCBA
            NAM -> _INIT_NAM t0 tminus tpr_minus tfp_minus tfp_plus ct_MD ct_IED ct_IPNR ct_CNTRL (fromJust ct_NT) ct_IPAC ct_DCC (Just ct_FER) ct_FEAC ct_FEB ct_SCEF ct_SCIXSD ct_PRF ct_PRCL ct_PRANX ct_PRNXT ct_IPCB ct_IPCBA
    in stateInitialisation initialState continue
