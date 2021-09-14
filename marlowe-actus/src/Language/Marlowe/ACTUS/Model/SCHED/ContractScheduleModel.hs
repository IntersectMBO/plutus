{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Model.SCHED.ContractScheduleModel where

import           Control.Applicative                                    (liftA2)
import           Control.Monad                                          (join, liftM4)
import           Data.List                                              as L (find, nub)
import           Data.Maybe                                             (fromMaybe, isJust, isNothing)
import           Data.Time                                              (LocalTime)
import           Data.Time.LocalTime                                    (addLocalTime)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (ContractTerms (..), Cycle (..),
                                                                         IPCB (IPCB_NTL), PPEF (..), PYTP (..),
                                                                         SCEF (..), ScheduleConfig)
import           Language.Marlowe.ACTUS.Definitions.Schedule            (ShiftedDay (..), ShiftedSchedule)
import           Language.Marlowe.ACTUS.Model.Utility.DateShift         (applyBDCWithCfg)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (generateRecurrentScheduleWithCorrections, inf,
                                                                         minusCycle, plusCycle, remove)

_S :: Maybe LocalTime -> Maybe Cycle -> Maybe LocalTime -> Maybe ScheduleConfig -> Maybe ShiftedSchedule
_S = liftM4 generateRecurrentScheduleWithCorrections

shift :: ScheduleConfig -> LocalTime -> ShiftedDay
shift = applyBDCWithCfg

-- Principal at Maturity (PAM)

_SCHED_IED_PAM :: ContractTerms -> Maybe [ShiftedDay]
_SCHED_IED_PAM ContractTerms{..} = (:[]) <$> liftA2 applyBDCWithCfg (Just scfg) ct_IED

_SCHED_MD_PAM :: ContractTerms -> Maybe [ShiftedDay]
_SCHED_MD_PAM ContractTerms{..} = (:[]) <$> liftA2 applyBDCWithCfg (Just scfg) ct_MD

_SCHED_PP_PAM :: ContractTerms -> Maybe ShiftedSchedule
_SCHED_PP_PAM ContractTerms{..} | ct_PPEF == Just PPEF_N = Nothing
_SCHED_PP_PAM ContractTerms{..} =
  let s | isNothing ct_OPANX && isNothing ct_OPCL = Nothing
        | isNothing ct_OPANX                      = liftA2 plusCycle ct_IED ct_OPCL
        | otherwise                               = ct_OPANX
   in _S s ct_OPCL ct_MD (Just scfg)

_SCHED_PY_PAM :: ContractTerms -> Maybe ShiftedSchedule
_SCHED_PY_PAM ContractTerms{..} | ct_PYTP == Just PYTP_O = Nothing
_SCHED_PY_PAM ct                                         = _SCHED_PP_PAM ct

_SCHED_FP_PAM :: ContractTerms -> Maybe ShiftedSchedule
_SCHED_FP_PAM ContractTerms{..} =
    let s | isNothing ct_FEANX && isNothing ct_FECL = Nothing
          | isNothing ct_FEANX                      = liftA2 plusCycle ct_IED ct_FECL
          | otherwise                               = ct_FEANX

        r | ct_FER == Just 0.0                      = Nothing
          | otherwise                               = _S s ((\c -> c {includeEndDay = True}) <$> ct_FECL) ct_MD (Just scfg)
    in r

_SCHED_PRD_PAM :: ContractTerms -> Maybe [ShiftedDay]
_SCHED_PRD_PAM ContractTerms{..} | isJust ct_PRD = (:[]) <$> liftA2 applyBDCWithCfg (Just scfg) ct_PRD
_SCHED_PRD_PAM _                                 = Nothing

_SCHED_TD_PAM :: ContractTerms -> Maybe [ShiftedDay]
_SCHED_TD_PAM ContractTerms{..} | isJust ct_TD = (:[]) <$> liftA2 applyBDCWithCfg (Just scfg) ct_TD
_SCHED_TD_PAM _                                = Nothing

_SCHED_IP_PAM :: ContractTerms -> Maybe [ShiftedDay]
_SCHED_IP_PAM ContractTerms{..} =
    let s | isNothing ct_IPANX && isNothing ct_IPCL = Nothing
          | isNothing ct_IPANX                      = liftA2 plusCycle ct_IED ct_IPCL
          | otherwise                               = ct_IPANX

        result | isNothing ct_IPNR                 = Nothing
               | otherwise                         = _S s ((\c -> c {includeEndDay = True }) <$> ct_IPCL) ct_MD (Just scfg)

        result' | isJust result && isJust ct_IPCED  = filter (\d -> Just (calculationDay d) > ct_IPCED) <$> result
                | otherwise                         = result
    in result'

_SCHED_IPCI_PAM :: ContractTerms -> Maybe [ShiftedDay]
_SCHED_IPCI_PAM ContractTerms{..} =
    let s | isNothing ct_IPANX && isNothing ct_IPCL = Nothing
          | isNothing ct_IPANX                      = liftA2 plusCycle ct_IED ct_IPCL
          | otherwise                               = ct_IPANX

        schedIP | isNothing ct_IPNR                 = Nothing
                | otherwise                         = _S s ((\c -> c { includeEndDay = True }) <$> ct_IPCL) ct_MD (Just scfg)

        result | isJust ct_IPCL && isJust ct_IPCED = let a = filter (\d -> Just (calculationDay d) < ct_IPCED) <$> schedIP
                                                         b = (:[]) <$> liftA2 applyBDCWithCfg (Just scfg) ct_IPCED
                                                      in liftA2 (++) a b
               | otherwise = Nothing
    in result

_SCHED_RR_PAM :: ContractTerms -> Maybe [ShiftedDay]
_SCHED_RR_PAM ContractTerms{..} =
    let s | isNothing ct_RRANX = liftA2 plusCycle ct_IED ct_RRCL
          | otherwise          = ct_RRANX

        tt   = _S s ((\c -> c { includeEndDay = False }) <$> ct_RRCL) ct_MD (Just scfg)
        trry = join $ liftA2 inf tt (Just ct_SD)

        result | isNothing ct_RRANX && isNothing ct_RRCL = Nothing
               | isJust ct_RRNXT                         = liftA2 remove trry tt
               | otherwise                               = tt
    in result

_SCHED_RRF_PAM :: ContractTerms -> Maybe ShiftedSchedule
_SCHED_RRF_PAM ContractTerms {..} =
    let s | isNothing ct_RRANX = liftA2 plusCycle ct_IED ct_RRCL
          | otherwise          = ct_RRANX

        tt = _S s ct_RRCL ct_MD (Just scfg)

        result | isNothing ct_RRANX && isNothing ct_RRCL = Nothing
               | otherwise                               = tt
    in
      if isJust ct_RRNXT then
        fmap (:[]) (L.find (\ShiftedDay{..} -> calculationDay > ct_SD) (fromMaybe [] result))
      else
        Nothing

_SCHED_SC_PAM :: ContractTerms -> Maybe ShiftedSchedule
_SCHED_SC_PAM ContractTerms{..} =
    let s | isNothing ct_SCANX && isNothing ct_SCCL = Nothing
          | isNothing ct_SCANX                      = liftA2 plusCycle ct_IED ct_SCCL
          | otherwise                               = ct_SCANX

        tt = _S s ((\c -> c { includeEndDay = False }) <$> ct_SCCL) ct_MD (Just scfg)

        result | ct_SCEF == Just SE_000 = Nothing
               | otherwise              = tt
    in result

-- Linear Amortizer (LAM)

_SCHED_PR_LAM :: ContractTerms -> Maybe ShiftedSchedule
_SCHED_PR_LAM ContractTerms{..} =
    let s | isNothing ct_PRANX && isNothing ct_PRCL = Nothing
          | isNothing ct_PRANX                      = liftA2 plusCycle ct_IED ct_PRCL
          | otherwise                               = ct_PRANX
     in _S s ((\c -> c { includeEndDay = False }) <$> ct_PRCL) ct_MD (Just scfg)

_SCHED_MD_LAM :: ContractTerms -> Maybe [ShiftedDay]
_SCHED_MD_LAM ContractTerms{..} = (:[]) <$> liftA2 applyBDCWithCfg (Just scfg) ct_MD

_SCHED_IPCB_LAM :: ContractTerms -> Maybe ShiftedSchedule
_SCHED_IPCB_LAM ContractTerms{..} =
    let s | isNothing ct_IPCBANX && isNothing ct_IPCBCL = Nothing
          | isNothing ct_IPCBANX                        = liftA2 plusCycle ct_IED ct_IPCBCL
          | otherwise                                   = ct_IPCBANX

        result | ct_IPCB /= Just IPCB_NTL = Nothing -- This means that IPCB != 'NTL', since there is no cycle
          | otherwise                = _S s ((\c -> c { includeEndDay = False }) <$> ct_IPCBCL) ct_MD (Just scfg)
    in result

-- Negative Amortizer (NAM)

_SCHED_IP_NAM :: ContractTerms -> Maybe [ShiftedDay]
_SCHED_IP_NAM ContractTerms{..} =
    let s | isNothing ct_PRANX = liftA2 plusCycle ct_IED ct_PRCL
          | otherwise          = ct_PRANX

        _T = liftA2 minusCycle s ct_PRCL

        r | isJust ct_IPANX = ct_IPANX
          | isJust ct_IPCL  = liftA2 plusCycle ct_IED ct_IPCL
          | otherwise       = Nothing

        u | isNothing ct_IPANX && isNothing ct_IPCL                        = Nothing
          | isJust ct_IPCED    && Just True == liftA2 (>) ct_IPCED _T = Nothing
          | otherwise                                                      = _S r ((\c -> c { includeEndDay = True }) <$> ct_IPCL) ct_MD (Just scfg)

        v = _S s ct_PRCL ct_MD (Just scfg)

        result = nub <$> liftA2 (++) u v

        result' | isJust result && isJust ct_IPCED = filter (\ShiftedDay{..} -> Just calculationDay > ct_IPCED) <$> result
                | otherwise = result
    in
        result'

_SCHED_IPCI_NAM :: ContractTerms -> Maybe [ShiftedDay]
_SCHED_IPCI_NAM ContractTerms{..} =
  let s | isNothing ct_PRANX = liftA2 plusCycle ct_IED ct_PRCL
          | otherwise          = ct_PRANX

      _T = liftA2 minusCycle s ct_PRCL

      r | isJust ct_IPCED = ct_IPCED
        | isJust ct_IPANX = ct_IPANX
        | isJust ct_IPCL  = liftA2 plusCycle ct_IED ct_IPCL
        | otherwise       = Nothing

      u | isNothing ct_IPANX && isNothing ct_IPCL                        = Nothing
        | isJust ct_IPCED    && Just True == liftA2 (>) ct_IPCED _T = Nothing
        | otherwise                                                      = _S r ((\c -> c { includeEndDay = True }) <$> ct_IPCL) ct_MD (Just scfg)

      v = _S s ct_PRCL ct_MD (Just scfg)

      result  = Just $ nub (fromMaybe [] u ++ fromMaybe [] v)

      result' | isJust result && isJust ct_IPCED = filter (\ShiftedDay{..} -> Just calculationDay <= ct_IPCED) <$> result
              | otherwise = Nothing
  in
      result'

-- Annuity (ANN)

_SCHED_PRF_ANN :: ContractTerms -> Maybe ShiftedSchedule
_SCHED_PRF_ANN ct@ContractTerms{..} =
  let prf | isJust ct_PRANX && isNothing ct_PRNXT && ct_PRANX > ct_IED = ct_PRANX >>= (\p -> Just [ShiftedDay p p]) . addLocalTime (-86400)
          | otherwise                                                  = Nothing
      rr  = _SCHED_RR_PAM ct
      rrf = _SCHED_RRF_PAM ct
  in Just $ fromMaybe [] prf ++ fromMaybe [] rr ++ fromMaybe [] rrf
