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
    let maybeS  =   if      isNothing _OPANX && isNothing _OPCL then Nothing
                    else if isNothing _OPANX                   then Just (_IED `plusCycle` (fromJust _OPCL)) 
                    else                                            _OPANX

    in case _PREF of 
        PREF_N -> Nothing
        PREF_Y -> F.fmap (\s -> _S s (fromJust _OPCL) _MD scfg) maybeS

_SCHED_PY_PAM scfg _PYTP _PREF _OPCL _IED _OPANX _MD = 
    case _PYTP of
        PYTP_O -> Nothing
        _      -> _SCHED_PP_PAM scfg _PREF _OPCL _IED _OPANX _MD

_SCHED_FP_PAM scfg _FER _FECL _IED _FEANX _MD = 
    let maybeS  =   if      isNothing _FEANX && isNothing _FECL then Nothing
                    else if isNothing _FEANX                   then Just (_IED `plusCycle` (fromJust _FECL)) 
                    else                                            _FEANX

    in if fromMaybe 0.0 _FER == 0.0 then Nothing
                                   else F.fmap (\s -> _S s (fromJust _FECL) _MD scfg) maybeS

_SCHED_PRD_PAM scfg _PRD = Just [shift scfg _PRD]

_SCHED_TD_PAM scfg _TD = Just [shift scfg _TD]

_SCHED_IP_PAM scfg _IPNR _IED _IPANX _IPCL _IPCED _MD = 
    let maybeS  =   if      isNothing _IPANX && isNothing _IPCL then Nothing
                    else if isJust _IPCED                      then _IPCED
                    else if isNothing _IPANX                   then Just (_IED `plusCycle` (fromJust _IPCL)) 
                    else                                            _IPANX

    in if isNothing _IPNR then Nothing
                          else F.fmap (\s -> _S s (fromJust _IPCL) _MD scfg) maybeS

