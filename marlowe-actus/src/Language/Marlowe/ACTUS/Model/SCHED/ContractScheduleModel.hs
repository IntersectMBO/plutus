{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Language.Marlowe.ACTUS.Model.SCHED.ContractScheduleModel where

import           Data.Maybe                                             (fromJust, isJust, isNothing, fromMaybe)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (PREF (..), PYTP (..), SCEF (..), ScheduleConfig(..), IPCB(IPCB_NTL), n)
import           Language.Marlowe.ACTUS.Model.Utility.DateShift         (applyBDCWithCfg)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (generateRecurrentScheduleWithCorrections, inf,
                                                                         plusCycle, shiftedPlusCycle, remove, sup)
import           Language.Marlowe.ACTUS.Definitions.Schedule      ()

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

-- - Linear Amortizer - --
_SCHED_IED_LAM = _SCHED_IED_PAM

_SCHED_PR_LAM scfg _PRCL _IED _PRANX _MD =
    let maybeS  | isNothing _PRANX && isNothing _PRCL = Nothing
                | isNothing _PRANX                   = Just $ _IED `plusCycle` fromJust _PRCL
                | otherwise                          = _PRANX
    in (\s -> _S s (fromJust _PRCL) (fromJust _MD) (scfg { includeEndDay = False })) <$> maybeS

_SCHED_MD_LAM scfg _IED _SD _PRANX _PRNXT _NT _PRCL _MD =
    let maybeTMinus | isJust _PRANX && ((fromJust _PRANX) >= _SD) = _PRANX
                    | (_IED `plusCycle` fromJust _PRCL) >= _SD = Just $ _IED `plusCycle` fromJust _PRCL
                    | otherwise                           = Nothing
        maybeSupPR | isNothing maybeTMinus = sup (fromMaybe [] $ _SCHED_PR_LAM scfg _PRCL _IED _PRANX _MD) _SD
                   | otherwise = Nothing
        result  | isJust _MD = Just [shift scfg $ fromJust _MD]
                | isJust maybeTMinus = Just [shift scfg $ (fromJust maybeTMinus) `plusCycle` ((fromJust _PRCL) { n = ((ceiling (_NT / (fromJust _PRNXT))) * (n (fromJust _PRCL))) })]
                | otherwise = Just [(fromJust maybeSupPR) `shiftedPlusCycle` ((fromJust _PRCL) { n = ((ceiling (_NT / (fromJust _PRNXT))) * (n (fromJust _PRCL))) })]
    in result

_SCHED_PP_LAM = _SCHED_PP_PAM

_SCHED_PY_LAM = _SCHED_PY_PAM

-- To avoid constraint error, we can't fixpoint this
_SCHED_FP_LAM scfg _FER _FECL _IED _FEANX _MD = _SCHED_FP_PAM scfg _FER _FECL _IED _FEANX _MD

_SCHED_PRD_LAM = _SCHED_PRD_PAM

_SCHED_TD_LAM = _SCHED_TD_PAM

_SCHED_IP_LAM = _SCHED_IP_PAM

_SCHED_IPCI_LAM = _SCHED_IPCI_PAM

_SCHED_IPCB_LAM scfg _IED _IPCB _IPCBCL _IPCBANX _MD =
    let maybeS  | isNothing _IPCBANX && isNothing _IPCBCL = Nothing
                | isNothing _IPCBANX                   = Just $ _IED `plusCycle` fromJust _IPCBCL
                | otherwise                          = _IPCBANX

        result  | (fromJust _IPCB) /= IPCB_NTL                   = Nothing -- This means that IPCB != 'NTL', since there is no cycle
                | otherwise                          = (\s -> _S s (fromJust _IPCBCL) _MD scfg) <$> maybeS
    in result

_SCHED_RR_LAM = _SCHED_RR_PAM

_SCHED_RRF_LAM = _SCHED_RRF_PAM

_SCHED_SC_LAM = _SCHED_SC_PAM
