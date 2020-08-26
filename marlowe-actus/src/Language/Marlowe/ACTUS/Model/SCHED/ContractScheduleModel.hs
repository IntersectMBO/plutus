{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Language.Marlowe.ACTUS.Model.SCHED.ContractScheduleModel where

import           Data.Maybe                                             (fromJust, isJust, isNothing)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (PREF (..), PYTP (..), SCEF (..))
import           Language.Marlowe.ACTUS.Model.Utility.DateShift         (applyBDCWithCfg)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (generateRecurrentScheduleWithCorrections, inf,
                                                                         plusCycle, remove)

_S = generateRecurrentScheduleWithCorrections
shift = applyBDCWithCfg

_SCHED_IED_PAM scfg _IED = Just [shift scfg _IED]

_SCHED_MD_PAM scfg tmd = Just [shift scfg tmd]

_SCHED_PP_PAM scfg _PREF _OPCL _IED _OPANX _MD =
    let maybeS  | isNothing _OPANX && isNothing _OPCL = Nothing
                | isNothing _OPANX                   = Just $ _IED `plusCycle` fromJust _OPCL
                | otherwise                          = _OPANX

    in case _PREF of
        PREF_N -> Nothing
        PREF_Y -> (\s -> _S s (fromJust _OPCL) _MD scfg) <$> maybeS

_SCHED_PY_PAM scfg _PYTP _PREF _OPCL _IED _OPANX _MD =
    case _PYTP of
        PYTP_O -> Nothing
        _      -> _SCHED_PP_PAM scfg _PREF _OPCL _IED _OPANX _MD

_SCHED_FP_PAM scfg _FER _FECL _IED _FEANX _MD =
    let maybeS  | isNothing _FEANX && isNothing _FECL = Nothing
                | isNothing _FEANX                   = Just $ _IED `plusCycle` fromJust _FECL
                | otherwise                          = _FEANX

        result  | _FER == 0.0                         = Nothing
                | otherwise                          = (\s -> _S s (fromJust _FECL) _MD scfg) <$> maybeS
    in result

_SCHED_PRD_PAM scfg _PRD = Just [shift scfg _PRD]

_SCHED_TD_PAM scfg _TD = Just [shift scfg _TD]

_SCHED_IP_PAM scfg _IPNR _IED _IPANX _IPCL _IPCED _MD =
    let maybeS  | isNothing _IPANX && isNothing _IPCL  = Nothing
                | isJust _IPCED                       = _IPCED
                | isNothing _IPANX                    = Just $ _IED `plusCycle` fromJust _IPCL
                | otherwise                           = _IPANX

        result  | isNothing _IPNR                     = Nothing
                | otherwise                           = (\s -> _S s (fromJust _IPCL) _MD scfg) <$> maybeS
    in result

_SCHED_IPCI_PAM scfg _IED _IPANX _IPCL _IPCED =
    let maybeS  | isNothing _IPANX && isNothing _IPCL  = Nothing
                | isNothing _IPANX                    = Just $ _IED `plusCycle` fromJust _IPCL
                | otherwise                           =  _IPANX

        result  | isNothing _IPCED                    = Nothing
                | otherwise                           = (\s -> _S s (fromJust _IPCL) (fromJust _IPCED) scfg) <$> maybeS
    in result

_SCHED_RR_PAM scfg _IED _SD _RRANX _RRCL _RRNXT _MD =
    let maybeS  | isNothing _RRANX                 = Just $ _IED `plusCycle` fromJust _RRCL
                | otherwise                           = _RRANX

        tt      = (\s -> _S s (fromJust _RRCL) _MD scfg) <$> maybeS
        trry    = fromJust $ inf (fromJust tt) _SD

        result  | isNothing _RRANX && isNothing _RRCL  = Nothing
                | isNothing _RRNXT                    = remove trry <$> tt
                | otherwise                           = tt
    in result

_SCHED_RRF_PAM scfg _IED _RRANX _RRCL _MD =
    let maybeS  | isNothing _RRANX                    = Just $ _IED `plusCycle` fromJust _RRCL
                | otherwise                           = _RRANX

        tt      = (\s -> _S s (fromJust _RRCL) _MD scfg) <$> maybeS

        result  | isNothing _RRANX && isNothing _RRCL  = Nothing
                | otherwise                           = tt
    in result

_SCHED_SC_PAM scfg _IED _SCEF _SCANX _SCCL _MD =
    let maybeS  | isNothing _SCANX && isNothing _SCCL  = Nothing
                | isNothing _SCANX                    = Just $ _IED `plusCycle` fromJust _SCCL
                | otherwise                           = _SCANX

        tt      = (\s -> _S s (fromJust _SCCL) _MD scfg) <$> maybeS

        result  | _SCEF == SE_000                      = Nothing
                | otherwise                           = tt
    in result

