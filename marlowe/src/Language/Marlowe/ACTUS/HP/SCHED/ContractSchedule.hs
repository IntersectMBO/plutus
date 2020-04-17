{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.HP.SCHED.ContractSchedule where

import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.ContractState
import Language.Marlowe.ACTUS.HP.BusinessEvents
import Language.Marlowe.ACTUS.HP.Schedule
import Language.Marlowe.ACTUS.HP.SCHED.PAM

schedule :: EventType -> ContractTerms -> ContractState -> Maybe [ShiftedDay]
schedule ev terms st@ContractState{..} = 
    case terms of 
        PamContractTerms{..} ->
            case ev of 
                IED -> _SCHED_IED_PAM scfg _IED
                MD  -> _SCHED_MD_PAM scfg tmd 
                PP  -> _SCHED_PP_PAM scfg _PREF _OPCL _IED _OPANX _MD