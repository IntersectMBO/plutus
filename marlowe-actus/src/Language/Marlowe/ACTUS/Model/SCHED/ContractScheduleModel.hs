module Language.Marlowe.ACTUS.Model.SCHED.ContractScheduleModel where

import           Data.Maybe                                             (fromJust, fromMaybe, isJust, isNothing)
import           Data.Time                                              (Day)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (Cycle (..), IPCB (IPCB_NTL), PPEF (..),
                                                                         PYTP (..), SCEF (..), ScheduleConfig)
import           Language.Marlowe.ACTUS.Definitions.Schedule            (ShiftedDay (..), ShiftedSchedule)
import           Language.Marlowe.ACTUS.Model.Utility.DateShift         (applyBDCWithCfg)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (generateRecurrentScheduleWithCorrections, inf,
                                                                         minusCycle, plusCycle, remove)

-- Principal at Maturity
_S :: Day -> Cycle -> Day -> ScheduleConfig -> ShiftedSchedule
_S = generateRecurrentScheduleWithCorrections

shift :: ScheduleConfig -> Day -> ShiftedDay
shift = applyBDCWithCfg

_SCHED_IED_PAM :: ScheduleConfig -> Day -> Maybe [ShiftedDay]
_SCHED_IED_PAM scfg _IED = Just [shift scfg _IED]

_SCHED_MD_PAM :: ScheduleConfig -> Day -> Maybe [ShiftedDay]
_SCHED_MD_PAM scfg tmd = Just [shift scfg tmd]

_SCHED_PP_PAM :: ScheduleConfig -> PPEF -> Maybe Cycle -> Day -> Maybe Day -> Day -> Maybe ShiftedSchedule
_SCHED_PP_PAM _    PPEF_N _OPCL _IED _OPANX _MD = Nothing
_SCHED_PP_PAM scfg _PREF  _OPCL _IED _OPANX _MD =
    let maybeS  | isNothing _OPANX && isNothing _OPCL = Nothing
                | isNothing _OPANX                    = Just $ _IED `plusCycle` fromJust _OPCL
                | otherwise                           = _OPANX
    in (\s -> _S s (fromJust _OPCL) _MD scfg) <$> maybeS

_SCHED_PY_PAM :: ScheduleConfig -> PYTP -> PPEF -> Maybe Cycle -> Day -> Maybe Day -> Day -> Maybe ShiftedSchedule
_SCHED_PY_PAM _    PYTP_O _PREF _OPCL _IED _OPANX _MD = Nothing
_SCHED_PY_PAM scfg _PYTP  _PREF _OPCL _IED _OPANX _MD = _SCHED_PP_PAM scfg _PREF _OPCL _IED _OPANX _MD

_SCHED_FP_PAM :: (Eq a, Fractional a) => ScheduleConfig -> a -> Maybe Cycle -> Day -> Maybe Day -> Day -> Maybe ShiftedSchedule
_SCHED_FP_PAM scfg _FER _FECL _IED _FEANX _MD =
    let maybeS  | isNothing _FEANX && isNothing _FECL = Nothing
                | isNothing _FEANX                    = Just $ _IED `plusCycle` fromJust _FECL
                | otherwise                           = _FEANX

        result  | _FER == 0.0                         = Nothing
                | otherwise                           = (\s -> _S s (fromJust _FECL){ includeEndDay = True } _MD scfg) <$> maybeS
    in result

_SCHED_PRD_PAM :: ScheduleConfig -> Maybe Day -> Maybe [ShiftedDay]
_SCHED_PRD_PAM scfg (Just _PRD) = Just [shift scfg _PRD]
_SCHED_PRD_PAM _ _              = Nothing

_SCHED_TD_PAM :: ScheduleConfig -> Maybe Day -> Maybe [ShiftedDay]
_SCHED_TD_PAM scfg (Just _TD) = Just [shift scfg _TD]
_SCHED_TD_PAM _    _          = Nothing

_SCHED_IP_PAM :: ScheduleConfig -> Maybe a -> Day -> Maybe Day -> Maybe Cycle -> Maybe Day -> Day -> Maybe [ShiftedDay]
_SCHED_IP_PAM scfg _IPNR _IED _IPANX _IPCL _IPCED _MD =
    let maybeS  | isNothing _IPANX && isNothing _IPCL = Nothing
                | isNothing _IPANX                    = Just $ _IED `plusCycle` fromJust _IPCL
                | otherwise                           = _IPANX

        result  | isNothing _IPNR                     = Nothing
                | otherwise                           = (\s -> _S s (fromJust _IPCL){ includeEndDay = True } _MD scfg) <$> maybeS

        result' | isJust result && isJust _IPCED      = Just $ filter (\ss -> calculationDay ss > fromJust _IPCED) $ fromJust result
                | otherwise                           = result
    in result'

_SCHED_IPCI_PAM :: ScheduleConfig -> Day -> Maybe Day -> Maybe Cycle -> Maybe Day -> Day -> Maybe a -> Maybe [ShiftedDay]
_SCHED_IPCI_PAM scfg _IED _IPANX _IPCL _IPCED _MD _IPNR =
    -- calculate IP sched:
    let maybeS  | isNothing _IPANX && isNothing _IPCL = Nothing
                | isNothing _IPANX                    = Just $ _IED `plusCycle` fromJust _IPCL
                | otherwise                           = _IPANX

        schedIP | isNothing _IPNR                     = Nothing
                | otherwise                           = (\s -> _S s (fromJust _IPCL){ includeEndDay = True } _MD scfg) <$> maybeS

        result  | isJust _IPCL && isJust _IPCED       = Just $ filter (\s -> calculationDay s < fromJust _IPCED) (fromJust schedIP) ++ [shift scfg $ fromJust _IPCED]
                | otherwise = Nothing
    in result

_SCHED_RR_PAM :: ScheduleConfig -> Day -> Day -> Maybe Day -> Maybe Cycle -> Maybe a -> Day -> Maybe [ShiftedDay]
_SCHED_RR_PAM scfg _IED _SD _RRANX _RRCL _RRNXT _MD =
    let maybeS  | isNothing _RRANX                    = Just $ _IED `plusCycle` fromJust _RRCL
                | otherwise                           = _RRANX

        tt      = (\s -> _S s (fromJust _RRCL){ includeEndDay = False } _MD scfg) <$> maybeS
        trry    = fromJust $ inf (fromJust tt) _SD

        result  | isNothing _RRANX && isNothing _RRCL = Nothing
                | isJust _RRNXT                       = remove trry <$> tt
                | otherwise                           = tt
    in result

_SCHED_RRF_PAM :: ScheduleConfig -> Day -> Maybe Day -> Maybe Cycle -> Day -> Maybe ShiftedSchedule
_SCHED_RRF_PAM scfg _IED _RRANX _RRCL _MD =
    let maybeS  | isNothing _RRANX                    = Just $ _IED `plusCycle` fromJust _RRCL
                | otherwise                           = _RRANX

        tt      = (\s -> _S s (fromJust _RRCL) _MD scfg) <$> maybeS

        result  | isNothing _RRANX && isNothing _RRCL = Nothing
                | otherwise                           = tt
    in result

_SCHED_SC_PAM :: ScheduleConfig -> Day -> SCEF -> Maybe Day -> Maybe Cycle -> Day -> Maybe ShiftedSchedule
_SCHED_SC_PAM scfg _IED _SCEF _SCANX _SCCL _MD =
    let maybeS  | isNothing _SCANX && isNothing _SCCL = Nothing
                | isNothing _SCANX                    = Just $ _IED `plusCycle` fromJust _SCCL
                | otherwise                           = _SCANX

        tt      = (\s -> _S s (fromJust _SCCL){ includeEndDay = False } _MD scfg) <$> maybeS

        result  | _SCEF == SE_000                     = Nothing
                | otherwise                           = tt
    in result

-- - Linear Amortizer - --
_SCHED_IED_LAM :: ScheduleConfig -> Day -> Maybe [ShiftedDay]
_SCHED_IED_LAM = _SCHED_IED_PAM

_SCHED_PR_LAM :: ScheduleConfig -> Maybe Cycle -> Day -> Maybe Day -> Day -> Maybe ShiftedSchedule
_SCHED_PR_LAM scfg _PRCL _IED _PRANX _MD =
    let maybeS  | isNothing _PRANX && isNothing _PRCL = Nothing
                | isNothing _PRANX                    = Just $ _IED `plusCycle` fromJust _PRCL
                | otherwise                           = _PRANX
    in (\s -> _S s (fromJust _PRCL) _MD scfg ) <$> maybeS

_SCHED_MD_LAM :: ScheduleConfig -> Day -> Maybe [ShiftedDay]
_SCHED_MD_LAM scfg tmd = Just [shift scfg tmd]

_SCHED_PP_LAM :: ScheduleConfig -> PPEF -> Maybe Cycle -> Day -> Maybe Day -> Day -> Maybe ShiftedSchedule
_SCHED_PP_LAM = _SCHED_PP_PAM

_SCHED_PY_LAM :: ScheduleConfig -> PYTP -> PPEF -> Maybe Cycle -> Day -> Maybe Day -> Day -> Maybe ShiftedSchedule
_SCHED_PY_LAM = _SCHED_PY_PAM

-- To avoid constraint error, we can't fixpoint this
_SCHED_FP_LAM :: (Eq a, Fractional a) => ScheduleConfig -> a -> Maybe Cycle -> Day -> Maybe Day -> Day -> Maybe ShiftedSchedule
_SCHED_FP_LAM = _SCHED_FP_PAM

_SCHED_PRD_LAM :: ScheduleConfig -> Maybe Day -> Maybe [ShiftedDay]
_SCHED_PRD_LAM = _SCHED_PRD_PAM

_SCHED_TD_LAM :: ScheduleConfig -> Maybe Day -> Maybe [ShiftedDay]
_SCHED_TD_LAM = _SCHED_TD_PAM

_SCHED_IP_LAM :: ScheduleConfig -> Maybe a -> Day -> Maybe Day -> Maybe Cycle -> Maybe Day -> Day -> Maybe [ShiftedDay]
_SCHED_IP_LAM = _SCHED_IP_PAM

_SCHED_IPCI_LAM :: ScheduleConfig -> Day -> Maybe Day -> Maybe Cycle -> Maybe Day -> Day -> Maybe a -> Maybe [ShiftedDay]
_SCHED_IPCI_LAM = _SCHED_IPCI_PAM

_SCHED_IPCB_LAM :: ScheduleConfig -> Day -> Maybe IPCB -> Maybe Cycle -> Maybe Day -> Day -> Maybe ShiftedSchedule
_SCHED_IPCB_LAM scfg _IED _IPCB _IPCBCL _IPCBANX _MD =
    let maybeS  | isNothing _IPCBANX && isNothing _IPCBCL = Nothing
                | isNothing _IPCBANX                      = Just $ _IED `plusCycle` fromJust _IPCBCL
                | otherwise                               = _IPCBANX

        result  | fromJust _IPCB /= IPCB_NTL              = Nothing -- This means that IPCB != 'NTL', since there is no cycle
                | otherwise                               = (\s -> _S s (fromJust _IPCBCL) _MD scfg) <$> maybeS
    in result

_SCHED_RR_LAM :: ScheduleConfig -> Day -> Day -> Maybe Day -> Maybe Cycle -> Maybe a -> Day -> Maybe [ShiftedDay]
_SCHED_RR_LAM = _SCHED_RR_PAM

_SCHED_RRF_LAM :: ScheduleConfig -> Day -> Maybe Day -> Maybe Cycle -> Day -> Maybe ShiftedSchedule
_SCHED_RRF_LAM = _SCHED_RRF_PAM

_SCHED_SC_LAM :: ScheduleConfig -> Day -> SCEF -> Maybe Day -> Maybe Cycle -> Day -> Maybe ShiftedSchedule
_SCHED_SC_LAM = _SCHED_SC_PAM

-- Negative Amortizer
_SCHED_IED_NAM :: ScheduleConfig -> Day -> Maybe [ShiftedDay]
_SCHED_IED_NAM = _SCHED_IED_PAM

_SCHED_PR_NAM :: ScheduleConfig -> Maybe Cycle -> Day -> Maybe Day -> Day -> Maybe ShiftedSchedule
_SCHED_PR_NAM = _SCHED_PR_LAM

_SCHED_MD_NAM :: ScheduleConfig -> Day -> Maybe [ShiftedDay]
_SCHED_MD_NAM = _SCHED_MD_PAM

_SCHED_PP_NAM :: ScheduleConfig -> PPEF -> Maybe Cycle -> Day -> Maybe Day -> Day -> Maybe ShiftedSchedule
_SCHED_PP_NAM = _SCHED_PP_PAM

_SCHED_PY_NAM :: ScheduleConfig -> PYTP -> PPEF -> Maybe Cycle -> Day -> Maybe Day -> Day -> Maybe ShiftedSchedule
_SCHED_PY_NAM = _SCHED_PY_PAM

_SCHED_FP_NAM :: (Eq a, Fractional a) => ScheduleConfig -> a -> Maybe Cycle -> Day -> Maybe Day -> Day -> Maybe ShiftedSchedule
_SCHED_FP_NAM = _SCHED_FP_PAM

_SCHED_PRD_NAM :: ScheduleConfig -> Maybe Day -> Maybe [ShiftedDay]
_SCHED_PRD_NAM = _SCHED_PRD_PAM

_SCHED_TD_NAM :: ScheduleConfig -> Maybe Day -> Maybe [ShiftedDay]
_SCHED_TD_NAM = _SCHED_TD_PAM

_SCHED_IP_NAM :: ScheduleConfig -> Day -> Maybe Cycle -> Maybe Day -> Maybe Day -> Maybe Day -> Maybe Cycle -> Day -> Maybe [ShiftedDay]
_SCHED_IP_NAM scfg _IED _PRCL _PRANX _IPCED _IPANX _IPCL _MD =
    let maybeS  | isNothing _PRANX = Just $ _IED `plusCycle` fromJust _PRCL
                | otherwise        = _PRANX

        _T      = fromJust maybeS `minusCycle` fromJust _PRCL

        r       | isJust _IPCED = _IPCED
                | isJust _IPANX = _IPANX
                | isJust _IPCL  = Just $ _IED `plusCycle` fromJust _IPCL
                | otherwise     = Nothing

        u       | isNothing _IPANX && isNothing _IPCL    = Nothing
                | isJust _IPCED && fromJust _IPCED >= _T = Nothing
                | otherwise                              = (\s -> _S s (fromJust _IPCL) _MD scfg) <$> r

        v       = (\s -> _S s (fromJust _PRCL) _MD scfg) <$> maybeS

        result  = Just (fromMaybe [] u ++ fromMaybe [] v)
    in
        result

_SCHED_IPCI_NAM :: ScheduleConfig -> Day -> Maybe Day -> Maybe Cycle -> Maybe Day -> Day -> Maybe a -> Maybe [ShiftedDay]
_SCHED_IPCI_NAM = _SCHED_IPCI_PAM

_SCHED_IPCB_NAM :: ScheduleConfig -> Day -> Maybe IPCB -> Maybe Cycle -> Maybe Day -> Day -> Maybe ShiftedSchedule
_SCHED_IPCB_NAM = _SCHED_IPCB_LAM

_SCHED_RR_NAM :: ScheduleConfig -> Day -> Day -> Maybe Day -> Maybe Cycle -> Maybe a -> Day -> Maybe [ShiftedDay]
_SCHED_RR_NAM = _SCHED_RR_PAM

_SCHED_RRF_NAM :: ScheduleConfig -> Day -> Maybe Day -> Maybe Cycle -> Day -> Maybe ShiftedSchedule
_SCHED_RRF_NAM = _SCHED_RRF_PAM

_SCHED_SC_NAM :: ScheduleConfig -> Day -> SCEF -> Maybe Day -> Maybe Cycle -> Day -> Maybe ShiftedSchedule
_SCHED_SC_NAM = _SCHED_SC_PAM
