{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Model.SCHED.ContractScheduleModel where

import           Control.Applicative                                    (liftA2)
import           Control.Monad                                          (liftM4)
import           Data.Functor                                           ((<&>))
import           Data.List                                              as L (find, nub)
import           Data.Maybe                                             (fromMaybe, isJust, isNothing, maybeToList)
import           Data.Time.LocalTime                                    (addLocalTime)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (ContractTerms, ContractTermsPoly (..),
                                                                         Cycle (..), IPCB (IPCB_NTL), PPEF (..),
                                                                         PYTP (..), SCEF (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule            (ShiftedDay (..))
import           Language.Marlowe.ACTUS.Model.Utility.DateShift         (applyBDCWithCfg)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (generateRecurrentScheduleWithCorrections, inf,
                                                                         remove, (<+>), (<->))
-- Principal at Maturity (PAM)

_SCHED_IED_PAM :: ContractTerms -> [ShiftedDay]
_SCHED_IED_PAM
  ContractTermsPoly
    { scfg = scheduleConfig,
      ct_IED = Just initialExchangeDate
    } = [applyBDCWithCfg scheduleConfig initialExchangeDate]
_SCHED_IED_PAM _ = []

_SCHED_MD_PAM :: ContractTerms -> [ShiftedDay]
_SCHED_MD_PAM
  ContractTermsPoly
    { scfg = scheduleConfig,
      ct_MD = Just maturityDate
    } = [applyBDCWithCfg scheduleConfig maturityDate]
_SCHED_MD_PAM _ = []

_SCHED_PP_PAM :: ContractTerms -> [ShiftedDay]
_SCHED_PP_PAM ContractTermsPoly {ct_PPEF = Just PPEF_N} = []
_SCHED_PP_PAM
  ContractTermsPoly
    { ct_OPANX = Just cycleAnchorDateOfOptionality,
      ct_OPCL = Just cycleOfOptionality,
      ct_MD = Just maturityDate,
      scfg = scheduleConfig
    } = generateRecurrentScheduleWithCorrections cycleAnchorDateOfOptionality cycleOfOptionality maturityDate scheduleConfig
_SCHED_PP_PAM
  ContractTermsPoly
    { ct_OPANX = Nothing,
      ct_OPCL = Just cycleOfOptionality,
      ct_MD = Just maturityDate,
      ct_IED = Just initialExchangeDate,
      scfg = scheduleConfig
    } = generateRecurrentScheduleWithCorrections (initialExchangeDate <+> cycleOfOptionality) cycleOfOptionality maturityDate scheduleConfig
_SCHED_PP_PAM _ = []

_SCHED_PY_PAM :: ContractTerms -> [ShiftedDay]
_SCHED_PY_PAM ContractTermsPoly {ct_PYTP = Just PYTP_O} = []
_SCHED_PY_PAM ct                                        = _SCHED_PP_PAM ct

_SCHED_FP_PAM :: ContractTerms -> [ShiftedDay]
_SCHED_FP_PAM ContractTermsPoly {ct_FER = Nothing} = []
_SCHED_FP_PAM ContractTermsPoly {ct_FER = Just 0.0} = []
_SCHED_FP_PAM
  ContractTermsPoly
    { ct_FEANX = Just cycleAnchorDateOfFee,
      ct_FECL = Just cycleOfFee,
      ct_MD = Just maturityDate,
      scfg = scheduleConfig
    } = generateRecurrentScheduleWithCorrections cycleAnchorDateOfFee cycleOfFee {includeEndDay = True} maturityDate scheduleConfig
_SCHED_FP_PAM
  ContractTermsPoly
    { ct_FEANX = Nothing,
      ct_FECL = Just cycleOfFee,
      ct_MD = Just maturityDate,
      ct_IED = Just initialExchangeDate,
      scfg = scheduleConfig
    } = generateRecurrentScheduleWithCorrections (initialExchangeDate <+> cycleOfFee) cycleOfFee {includeEndDay = True} maturityDate scheduleConfig
_SCHED_FP_PAM _ = []

_SCHED_PRD_PAM :: ContractTerms -> [ShiftedDay]
_SCHED_PRD_PAM
  ContractTermsPoly
    { scfg = scheduleConfig,
      ct_PRD = Just purchaseDate
    } = [applyBDCWithCfg scheduleConfig purchaseDate]
_SCHED_PRD_PAM _ = []

_SCHED_TD_PAM :: ContractTerms -> [ShiftedDay]
_SCHED_TD_PAM
  ContractTermsPoly
    { scfg = scheduleConfig,
      ct_TD = Just terminationDate
    } = [applyBDCWithCfg scheduleConfig terminationDate]
_SCHED_TD_PAM _ = []

_SCHED_IP_PAM :: ContractTerms -> [ShiftedDay]
_SCHED_IP_PAM
  ContractTermsPoly
    { ct_IPANX = Just cycleAnchorOfInterestPayment,
      ct_IPCL = Just cycleOfInterestPayment,
      ct_MD = Just maturityDate,
      ct_IPCED = capitalizationEndDate,
      scfg = scheduleConfig
    } =
    let s = generateRecurrentScheduleWithCorrections cycleAnchorOfInterestPayment cycleOfInterestPayment {includeEndDay = True} maturityDate scheduleConfig
     in filter (\d -> Just (calculationDay d) > capitalizationEndDate) s
_SCHED_IP_PAM
  ContractTermsPoly
    { ct_IPANX = Nothing,
      ct_IPCL = Just cycleOfInterestPayment,
      ct_MD = Just maturityDate,
      ct_IED = Just initialExchangeDate,
      ct_IPCED = capitalizationEndDate,
      scfg = scheduleConfig
    } =
    let s = generateRecurrentScheduleWithCorrections (initialExchangeDate <+> cycleOfInterestPayment) cycleOfInterestPayment {includeEndDay = True} maturityDate scheduleConfig
     in filter (\d -> Just (calculationDay d) > capitalizationEndDate) s
_SCHED_IP_PAM _ = []

_SCHED_IPCI_PAM :: ContractTerms -> [ShiftedDay]
_SCHED_IPCI_PAM
  ContractTermsPoly
    { ct_IPANX = Just cycleAnchorOfInterestPayment,
      ct_IPCL = Just cycleOfInterestPayment,
      ct_MD = Just maturityDate,
      ct_IPCED = Just capitalizationEndDate,
      scfg = scheduleConfig
    } =
    let s = generateRecurrentScheduleWithCorrections cycleAnchorOfInterestPayment cycleOfInterestPayment {includeEndDay = True} maturityDate scheduleConfig
     in filter (\d -> calculationDay d < capitalizationEndDate) s ++ [applyBDCWithCfg scheduleConfig capitalizationEndDate]
_SCHED_IPCI_PAM
  ContractTermsPoly
    { ct_IPANX = Nothing,
      ct_IPCL = Just cycleOfInterestPayment,
      ct_MD = Just maturityDate,
      ct_IED = Just initialExchangeDate,
      ct_IPCED = Just capitalizationEndDate,
      scfg = scheduleConfig
    } =
    let s = generateRecurrentScheduleWithCorrections (initialExchangeDate <+> cycleOfInterestPayment) cycleOfInterestPayment {includeEndDay = True} maturityDate scheduleConfig
     in filter (\d -> calculationDay d < capitalizationEndDate) s ++ [applyBDCWithCfg scheduleConfig capitalizationEndDate]
_SCHED_IPCI_PAM _ = []

_SCHED_RR_PAM :: ContractTerms -> [ShiftedDay]
_SCHED_RR_PAM
  ContractTermsPoly
    { ct_RRANX = Just cycleAnchorOfRateReset,
      ct_RRCL = Just cycleOfRateReset,
      ct_RRNXT = Just _,
      ct_MD = Just maturityDate,
      ct_SD = statusDate,
      scfg = scheduleConfig
    } =
    let tt = generateRecurrentScheduleWithCorrections cycleAnchorOfRateReset cycleOfRateReset {includeEndDay = False} maturityDate scheduleConfig
     in fromMaybe [] (inf tt statusDate <&> flip remove tt)
_SCHED_RR_PAM
  ContractTermsPoly
    { ct_RRANX = Just cycleAnchorOfRateReset,
      ct_RRCL = Just cycleOfRateReset,
      ct_RRNXT = Nothing,
      ct_MD = Just maturityDate,
      scfg = scheduleConfig
    } = generateRecurrentScheduleWithCorrections cycleAnchorOfRateReset cycleOfRateReset {includeEndDay = False} maturityDate scheduleConfig
_SCHED_RR_PAM
  ContractTermsPoly
    { ct_RRANX = Nothing,
      ct_RRCL = Just cycleOfRateReset,
      ct_RRNXT = Just _,
      ct_MD = Just maturityDate,
      ct_IED = Just initialExchangeDate,
      ct_SD = statusDate,
      scfg = scheduleConfig
    } =
    let tt = generateRecurrentScheduleWithCorrections (initialExchangeDate <+> cycleOfRateReset) cycleOfRateReset {includeEndDay = False} maturityDate scheduleConfig
     in fromMaybe [] (inf tt statusDate <&> flip remove tt)
_SCHED_RR_PAM
  ContractTermsPoly
    { ct_RRANX = Nothing,
      ct_RRCL = Just cycleOfRateReset,
      ct_RRNXT = Nothing,
      ct_MD = Just maturityDate,
      ct_IED = Just initialExchangeDate,
      scfg = scheduleConfig
    } = generateRecurrentScheduleWithCorrections (initialExchangeDate <+> cycleOfRateReset) cycleOfRateReset {includeEndDay = False} maturityDate scheduleConfig
_SCHED_RR_PAM _ = []

_SCHED_RRF_PAM :: ContractTerms -> [ShiftedDay]
_SCHED_RRF_PAM
  ContractTermsPoly
    { ct_RRANX = Just cycleAnchorOfRateReset,
      ct_RRCL = Just cycleOfRateReset,
      ct_RRNXT = Just _,
      ct_MD = Just maturityDate,
      ct_SD = statusDate,
      scfg = scheduleConfig
    } =
    let tt = generateRecurrentScheduleWithCorrections cycleAnchorOfRateReset cycleOfRateReset {includeEndDay = False} maturityDate scheduleConfig
     in maybeToList (L.find (\ShiftedDay{..} -> calculationDay > statusDate) tt)
_SCHED_RRF_PAM
  ContractTermsPoly
    { ct_RRANX = Nothing,
      ct_RRCL = Just cycleOfRateReset,
      ct_RRNXT = Just _,
      ct_MD = Just maturityDate,
      ct_IED = Just initialExchangeDate,
      ct_SD = statusDate,
      scfg = scheduleConfig
    } =
    let tt = generateRecurrentScheduleWithCorrections (initialExchangeDate <+> cycleOfRateReset) cycleOfRateReset maturityDate scheduleConfig
     in maybeToList (L.find (\ShiftedDay{..} -> calculationDay > statusDate) tt)
_SCHED_RRF_PAM _ = []

_SCHED_SC_PAM :: ContractTerms -> [ShiftedDay]
_SCHED_SC_PAM ContractTermsPoly {ct_SCEF = Just SE_000} = []
_SCHED_SC_PAM
  ContractTermsPoly
    { ct_SCANX = Just cycleAnchorOfScalingIndex,
      ct_SCCL = Just cycleOfScalingIndex,
      ct_MD = Just maturityDate,
      scfg = scheduleConfig
    } = generateRecurrentScheduleWithCorrections cycleAnchorOfScalingIndex cycleOfScalingIndex {includeEndDay = False} maturityDate scheduleConfig
_SCHED_SC_PAM
  ContractTermsPoly
    { ct_SCANX = Nothing,
      ct_SCCL = Just cycleOfScalingIndex,
      ct_MD = Just maturityDate,
      ct_IED = Just initialExchangeDate,
      scfg = scheduleConfig
    } = generateRecurrentScheduleWithCorrections (initialExchangeDate <+> cycleOfScalingIndex) cycleOfScalingIndex {includeEndDay = False} maturityDate scheduleConfig
_SCHED_SC_PAM _ = []

-- Linear Amortizer (LAM)

_SCHED_PR_LAM :: ContractTerms -> [ShiftedDay]
_SCHED_PR_LAM
  ContractTermsPoly
    { ct_PRANX = Just cycleAnchorOfPrincipalRedemption,
      ct_PRCL = Just cycleOfPrincipalRedemption,
      ct_MD = Just maturityDate,
      scfg = scheduleConfig
    } = generateRecurrentScheduleWithCorrections cycleAnchorOfPrincipalRedemption cycleOfPrincipalRedemption {includeEndDay = False} maturityDate scheduleConfig
_SCHED_PR_LAM
  ContractTermsPoly
    { ct_PRANX = Nothing,
      ct_PRCL = Just cycleOfPrincipalRedemption,
      ct_MD = Just maturityDate,
      ct_IED = Just initialExchangeDate,
      scfg = scheduleConfig
    } = generateRecurrentScheduleWithCorrections (initialExchangeDate <+> cycleOfPrincipalRedemption) cycleOfPrincipalRedemption {includeEndDay = False} maturityDate scheduleConfig
_SCHED_PR_LAM _ = []

_SCHED_MD_LAM :: ContractTerms -> [ShiftedDay]
_SCHED_MD_LAM
  ContractTermsPoly
    { ct_MD = Just maturityDate,
      scfg = scheduleConfig
    } = [applyBDCWithCfg scheduleConfig maturityDate]
_SCHED_MD_LAM _ = []

_SCHED_IPCB_LAM :: ContractTerms -> [ShiftedDay]
_SCHED_IPCB_LAM ContractTermsPoly {..} | ct_IPCB /= Just IPCB_NTL = []
_SCHED_IPCB_LAM
  ContractTermsPoly
    { ct_IPCBANX = Just cycleAnchorOfInterestBaseCalculation,
      ct_IPCBCL = Just cycleOfInterestBaseCalculation,
      ct_MD = Just maturityDate,
      scfg = scheduleConfig
    } = generateRecurrentScheduleWithCorrections cycleAnchorOfInterestBaseCalculation cycleOfInterestBaseCalculation {includeEndDay = False} maturityDate scheduleConfig
_SCHED_IPCB_LAM
  ContractTermsPoly
    { ct_IPCBANX = Nothing,
      ct_IPCBCL = Just cycleOfInterestBaseCalculation,
      ct_MD = Just maturityDate,
      ct_IED = Just initialExchangeDate,
      scfg = scheduleConfig
    } = generateRecurrentScheduleWithCorrections (initialExchangeDate <+> cycleOfInterestBaseCalculation) cycleOfInterestBaseCalculation {includeEndDay = False} maturityDate scheduleConfig
_SCHED_IPCB_LAM _ = []

-- Negative Amortizer (NAM)

_SCHED_IP_NAM :: ContractTerms -> [ShiftedDay]
_SCHED_IP_NAM ContractTermsPoly {..} =
  let s
        | isNothing ct_PRANX = liftA2 (<+>) ct_IED ct_PRCL
        | otherwise = ct_PRANX

      v = liftM4 generateRecurrentScheduleWithCorrections s ct_PRCL ct_MD (Just scfg)

      r
        | isJust ct_IPANX = ct_IPANX
        | isJust ct_IPCL = liftA2 (<+>) ct_IED ct_IPCL
        | otherwise = Nothing

      _T = liftA2 (<->) s ct_PRCL

      u
        | isNothing ct_IPANX && isNothing ct_IPCL = Nothing
        | isJust ct_IPCED && Just True == liftA2 (>) ct_IPCED _T = Nothing
        | otherwise = liftM4 generateRecurrentScheduleWithCorrections r ((\c -> c {includeEndDay = True}) <$> ct_IPCL) ct_MD (Just scfg)

      result = nub <$> liftA2 (++) u v

      result'
        | isJust result && isJust ct_IPCED = filter (\ShiftedDay {..} -> Just calculationDay > ct_IPCED) <$> result
        | otherwise = result
   in fromMaybe [] result'

_SCHED_IPCI_NAM :: ContractTerms -> [ShiftedDay]
_SCHED_IPCI_NAM ContractTermsPoly {..} =
  let s
        | isNothing ct_PRANX = liftA2 (<+>) ct_IED ct_PRCL
        | otherwise = ct_PRANX

      v = liftM4 generateRecurrentScheduleWithCorrections s ct_PRCL ct_MD (Just scfg)

      r
        | isJust ct_IPCED = ct_IPCED
        | isJust ct_IPANX = ct_IPANX
        | isJust ct_IPCL = liftA2 (<+>) ct_IED ct_IPCL
        | otherwise = Nothing

      _T = liftA2 (<->) s ct_PRCL

      u
        | isNothing ct_IPANX && isNothing ct_IPCL = Nothing
        | isJust ct_IPCED && Just True == liftA2 (>) ct_IPCED _T = Nothing
        | otherwise = liftM4 generateRecurrentScheduleWithCorrections r ((\c -> c {includeEndDay = True}) <$> ct_IPCL) ct_MD (Just scfg)

      result = Just $ nub (fromMaybe [] u ++ fromMaybe [] v)

      result'
        | isJust result && isJust ct_IPCED = filter (\ShiftedDay {..} -> Just calculationDay <= ct_IPCED) <$> result
        | otherwise = Nothing
   in fromMaybe [] result'

-- Annuity (ANN)

_SCHED_PRF_ANN :: ContractTerms -> [ShiftedDay]
_SCHED_PRF_ANN
  ct@ContractTermsPoly
    { ct_PRANX = Just cycleAnchorOfPrincipalRedemption,
      ct_PRNXT = Nothing,
      ct_IED = Just initialExchangeDate
    } =
    let prf
          | cycleAnchorOfPrincipalRedemption > initialExchangeDate = let p = addLocalTime (-86400) cycleAnchorOfPrincipalRedemption in [ShiftedDay p p]
          | otherwise = []
        rr = _SCHED_RR_PAM ct
        rrf = _SCHED_RRF_PAM ct
     in prf ++ rr ++ rrf
_SCHED_PRF_ANN _ = []
