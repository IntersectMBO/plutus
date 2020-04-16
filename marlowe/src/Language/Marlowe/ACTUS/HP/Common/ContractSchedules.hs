{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.HP.Common.ContractSchedules where

import Language.Marlowe.ACTUS.HP.Utility.ScheduleGenerator
import Language.Marlowe.ACTUS.HP.Utility.DateShift
import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.ContractState
import Language.Marlowe.ACTUS.HP.BusinessEvents
import Language.Marlowe.ACTUS.HP.Schedule
import Data.Time
import Data.Maybe
import qualified Data.Functor as F

_S = generateRecurrentScheduleWithCorrections
shift = applyBDCWithCfg

schedule :: EventType -> ContractTerms -> ContractState -> Maybe [ShiftedDay]
schedule ev terms@PamContractTerms{..} st@ContractState{..} = 
    case ev of 
        IED -> Just [shift scfg _IED]
        MD -> Just [shift scfg tmd]
        PP -> case _PREF of 
            PREF_N -> Nothing
            PREF_Y ->    let maybeS = if isNothing _OPANX && isNothing _OPCL then Nothing
                             else if isNothing _OPANX then Just (_IED `plusCycle` (fromJust _OPCL)) 
                             else _OPANX
                        in F.fmap (\s -> _S s (fromJust _OPCL) _MD scfg) maybeS