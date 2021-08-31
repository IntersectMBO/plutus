{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Model.INIT.StateInitialization where

import           Data.Maybe                                                 (fromJust, maybeToList)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents          (EventType (FP, IP, PR))
import           Language.Marlowe.ACTUS.Definitions.ContractState           (ContractState)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms           (CT (..), ContractTerms (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule                (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (_INIT_ANN, _INIT_LAM, _INIT_NAM, _INIT_PAM)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule        (schedule)
import           Language.Marlowe.ACTUS.Model.Utility.ANN.Maturity          (maturity)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator     (inf, sup)
import           Language.Marlowe.ACTUS.Ops                                 (YearFractionOps (_y))

initializeState :: ContractTerms -> ContractState
initializeState terms@ContractTerms {..} =
    let t0         = ct_SD
        -- PAM
        fpSchedule         = schedule FP terms
        tfp_minus          = maybe t0 calculationDay ((\sc -> sup sc t0) =<< fpSchedule)
        tfp_plus           = maybe t0 calculationDay ((\sc -> inf sc t0) =<< fpSchedule)
        ipSchedule         = schedule IP terms
        tminus             = maybe t0 calculationDay ((\sc -> sup sc t0) =<< ipSchedule)

        -- LAM, NAM, ANN
        prSchedule         = schedule PR terms
        tpr_minus          = maybe t0 calculationDay ((\sc -> sup sc t0) =<< prSchedule)

    in  case contractType of
        PAM -> _INIT_PAM t0 tminus tfp_minus tfp_plus terms
        LAM -> _INIT_LAM t0 tminus tpr_minus tfp_minus tfp_plus terms
        NAM -> _INIT_NAM t0 tminus tpr_minus tfp_minus tfp_plus terms
        ANN -> let prDates            = maybe [] (map calculationDay) prSchedule ++ maybeToList (maturity terms)
                   ti                 = zipWith (\tn tm -> _y (fromJust ct_DCC) tn tm ct_MD) prDates (tail prDates)
                in _INIT_ANN t0 tminus tpr_minus tfp_minus tfp_plus ti terms

