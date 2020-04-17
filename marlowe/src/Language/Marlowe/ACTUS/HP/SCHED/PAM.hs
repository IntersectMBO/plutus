module Language.Marlowe.ACTUS.HP.SCHED.PAM where

import Language.Marlowe.ACTUS.HP.Utility.ScheduleGenerator
import Language.Marlowe.ACTUS.HP.Utility.DateShift
import Language.Marlowe.ACTUS.HP.Schedule
import Data.Time
import Data.Maybe
import qualified Data.Functor as F
import Language.Marlowe.ACTUS.HP.ContractTerms

_S = generateRecurrentScheduleWithCorrections
shift = applyBDCWithCfg

_SCHED_IED_PAM scfg _IED = Just [shift scfg _IED]

_SCHED_MD_PAM scfg tmd = Just [shift scfg tmd]

_SCHED_PP_PAM scfg _PREF _OPCL _IED _OPANX _MD = 
    case _PREF of 
        PREF_N ->    Nothing
        PREF_Y ->    let maybeS = if isNothing _OPANX && isNothing _OPCL then Nothing
                            else if isNothing _OPANX then Just (_IED `plusCycle` (fromJust _OPCL)) 
                            else _OPANX
                    in F.fmap (\s -> _S s (fromJust _OPCL) _MD scfg) maybeS