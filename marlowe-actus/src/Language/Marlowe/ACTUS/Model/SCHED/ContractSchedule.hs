{-# LANGUAGE RecordWildCards #-}

{-| = ACTUS contract schedules

The implementation is a transliteration of the ACTUS specification v1.1

-}

module Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule
  ( schedule
  , maturity
  )
where

import           Control.Applicative                                      (Alternative ((<|>)))
import           Data.Ord                                                 (Down (..))
import           Data.Sort                                                (sortOn)
import           Data.Time                                                (Day)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents        (EventType (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms         (CT (..), ContractTerms (..), Cycle (..),
                                                                           ScheduleConfig (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule              (ShiftedDay (..))
import           Language.Marlowe.ACTUS.Model.SCHED.ContractScheduleModel
import           Language.Marlowe.ACTUS.Model.Utility.DateShift           (applyBDCWithCfg)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator   (applyEOMC,
                                                                           generateRecurrentScheduleWithCorrections,
                                                                           (<+>), (<->))
import           Language.Marlowe.ACTUS.Model.Utility.YearFraction        (yearFraction)
import           Language.Marlowe.ACTUS.Ops                               (YearFractionOps (_y))

schedule :: EventType -> ContractTerms -> Maybe [ShiftedDay]
schedule ev c = let m = maturity c in schedule' ev c { ct_MD = m }
  where

    schedule' :: EventType -> ContractTerms -> Maybe [ShiftedDay]
    schedule' IED  ct@ContractTerms{ contractType = PAM } = _SCHED_IED_PAM ct
    schedule' MD   ct@ContractTerms{ contractType = PAM } = _SCHED_MD_PAM ct
    schedule' PP   ct@ContractTerms{ contractType = PAM } = _SCHED_PP_PAM ct
    schedule' PY   ct@ContractTerms{ contractType = PAM } = _SCHED_PY_PAM ct
    schedule' FP   ct@ContractTerms{ contractType = PAM } = _SCHED_FP_PAM ct
    schedule' PRD  ct@ContractTerms{ contractType = PAM } = _SCHED_PRD_PAM ct
    schedule' TD   ct@ContractTerms{ contractType = PAM } = _SCHED_TD_PAM ct
    schedule' IP   ct@ContractTerms{ contractType = PAM } = _SCHED_IP_PAM ct
    schedule' IPCI ct@ContractTerms{ contractType = PAM } = _SCHED_IPCI_PAM ct
    schedule' RR   ct@ContractTerms{ contractType = PAM } = _SCHED_RR_PAM ct
    schedule' RRF  ct@ContractTerms{ contractType = PAM } = _SCHED_RRF_PAM ct
    schedule' SC   ct@ContractTerms{ contractType = PAM } = _SCHED_SC_PAM ct

    schedule' IED  ct@ContractTerms{ contractType = LAM } = _SCHED_IED_PAM ct
    schedule' PR   ct@ContractTerms{ contractType = LAM } = _SCHED_PR_LAM ct
    schedule' MD   ct@ContractTerms{ contractType = LAM } = _SCHED_MD_LAM ct
    schedule' PP   ct@ContractTerms{ contractType = LAM } = _SCHED_PP_PAM ct
    schedule' PY   ct@ContractTerms{ contractType = LAM } = _SCHED_PY_PAM ct
    schedule' FP   ct@ContractTerms{ contractType = LAM } = _SCHED_FP_PAM ct
    schedule' PRD  ct@ContractTerms{ contractType = LAM } = _SCHED_PRD_PAM ct
    schedule' TD   ct@ContractTerms{ contractType = LAM } = _SCHED_TD_PAM ct
    schedule' IP   ct@ContractTerms{ contractType = LAM } = _SCHED_IP_PAM ct
    schedule' IPCI ct@ContractTerms{ contractType = LAM } = _SCHED_IPCI_PAM ct
    schedule' IPCB ct@ContractTerms{ contractType = LAM } = _SCHED_IPCB_LAM ct
    schedule' RR   ct@ContractTerms{ contractType = LAM } = _SCHED_RR_PAM ct
    schedule' RRF  ct@ContractTerms{ contractType = LAM } = _SCHED_RRF_PAM ct
    schedule' SC   ct@ContractTerms{ contractType = LAM } = _SCHED_SC_PAM ct

    schedule' IED  ct@ContractTerms{ contractType = NAM } = _SCHED_IED_PAM ct
    schedule' PR   ct@ContractTerms{ contractType = NAM } = _SCHED_PR_LAM ct
    schedule' MD   ct@ContractTerms{ contractType = NAM } = _SCHED_MD_PAM ct
    schedule' PP   ct@ContractTerms{ contractType = NAM } = _SCHED_PP_PAM ct
    schedule' PY   ct@ContractTerms{ contractType = NAM } = _SCHED_PY_PAM ct
    schedule' FP   ct@ContractTerms{ contractType = NAM } = _SCHED_FP_PAM ct
    schedule' PRD  ct@ContractTerms{ contractType = NAM } = _SCHED_PRD_PAM ct
    schedule' TD   ct@ContractTerms{ contractType = NAM } = _SCHED_TD_PAM ct
    schedule' IP   ct@ContractTerms{ contractType = NAM } = _SCHED_IP_NAM ct
    schedule' IPCI ct@ContractTerms{ contractType = NAM } = _SCHED_IPCI_NAM ct
    schedule' IPCB ct@ContractTerms{ contractType = NAM } = _SCHED_IPCB_LAM ct
    schedule' RR   ct@ContractTerms{ contractType = NAM } = _SCHED_RR_PAM ct
    schedule' RRF  ct@ContractTerms{ contractType = NAM } = _SCHED_RRF_PAM ct
    schedule' SC   ct@ContractTerms{ contractType = NAM } = _SCHED_SC_PAM ct

    schedule' IED  ct@ContractTerms{ contractType = ANN } = _SCHED_IED_PAM ct
    schedule' PR   ct@ContractTerms{ contractType = ANN } = _SCHED_PR_LAM ct
    schedule' MD   ct@ContractTerms{ contractType = ANN } = _SCHED_MD_PAM c { ct_MD = ct_MD c <|> ct_MD ct }
    schedule' PP   ct@ContractTerms{ contractType = ANN } = _SCHED_PP_PAM ct
    schedule' PY   ct@ContractTerms{ contractType = ANN } = _SCHED_PY_PAM ct
    schedule' FP   ct@ContractTerms{ contractType = ANN } = _SCHED_FP_PAM ct
    schedule' PRD  ct@ContractTerms{ contractType = ANN } = _SCHED_PRD_PAM ct
    schedule' TD   ct@ContractTerms{ contractType = ANN } = _SCHED_TD_PAM ct
    schedule' IP   ct@ContractTerms{ contractType = ANN } = _SCHED_IP_NAM c { ct_MD = ct_MD c <|> ct_MD ct }
    schedule' IPCI ct@ContractTerms{ contractType = ANN } = _SCHED_IPCI_PAM ct
    schedule' IPCB ct@ContractTerms{ contractType = ANN } = _SCHED_IPCB_LAM ct
    schedule' RR   ct@ContractTerms{ contractType = ANN } = _SCHED_RR_PAM ct
    schedule' RRF  ct@ContractTerms{ contractType = ANN } = _SCHED_RRF_PAM ct
    schedule' SC   ct@ContractTerms{ contractType = ANN } = _SCHED_SC_PAM ct
    schedule' PRF  ct@ContractTerms{ contractType = ANN } = _SCHED_PRF_ANN ct

    schedule' _ _                                         = Nothing

maturity :: ContractTerms -> Maybe Day
maturity ContractTerms {contractType = PAM, ..} = ct_MD
maturity ContractTerms {contractType = LAM, ct_MD = md@(Just _)} = md
maturity
  ContractTerms
    { contractType = LAM,
      ct_MD = Nothing,
      ct_PRANX = Just principalRedemptionAnchor,
      ct_IPCL = Just interestPaymentCycle,
      ct_PRCL = Just principalRedemptionCycle,
      ct_PRNXT = Just nextPrincipalRedemptionPayment,
      ct_NT = Just notionalPrincipal,
      ct_SD = statusDate,
      scfg = scheduleConfig
    } =
    let (lastEvent, remainingPeriods)
          | principalRedemptionAnchor < statusDate =
            let previousEvents = generateRecurrentScheduleWithCorrections principalRedemptionAnchor principalRedemptionCycle statusDate scheduleConfig
                f1 = (\ShiftedDay {..} -> calculationDay > statusDate <-> interestPaymentCycle)
                f2 = (\ShiftedDay {..} -> calculationDay == statusDate)
                ShiftedDay {calculationDay = lastEventCalcDay} = head . filter f2 . filter f1 $ previousEvents
             in (lastEventCalcDay, notionalPrincipal / nextPrincipalRedemptionPayment)
          | otherwise = (principalRedemptionAnchor, notionalPrincipal / nextPrincipalRedemptionPayment - 1)
        m = lastEvent <+> (principalRedemptionCycle {n = n principalRedemptionCycle * round remainingPeriods :: Integer})
     in eomc scheduleConfig >>= \d -> return $ applyEOMC lastEvent principalRedemptionCycle d m
maturity ContractTerms {contractType = NAM, ct_MD = md@(Just _)} = md
maturity
  ContractTerms
    { contractType = NAM,
      ct_MD = Nothing,
      ct_PRANX = Just principalRedemptionAnchor,
      ct_PRNXT = Just nextPrincipalRedemptionPayment,
      ct_IED = Just initialExchangeDate,
      ct_PRCL = Just principalRedemptionCycle,
      ct_NT = Just notionalPrincipal,
      ct_IPNR = Just nominalInterestRate,
      ct_DCC = Just dayCountConvention,
      ct_SD = statusDate,
      scfg = scheduleConfig
    } =
    let lastEvent
          | principalRedemptionAnchor >= statusDate = principalRedemptionAnchor
          | initialExchangeDate <+> principalRedemptionCycle >= statusDate = initialExchangeDate <+> principalRedemptionCycle
          | otherwise =
            let previousEvents = generateRecurrentScheduleWithCorrections principalRedemptionAnchor principalRedemptionCycle statusDate scheduleConfig
                f = (\ShiftedDay {..} -> calculationDay == statusDate)
                ShiftedDay {calculationDay = lastEventCalcDay} = head . filter f $ previousEvents
             in lastEventCalcDay

        yLastEventPlusPRCL = yearFraction dayCountConvention lastEvent (lastEvent <+> principalRedemptionCycle) Nothing
        redemptionPerCycle = nextPrincipalRedemptionPayment - (yLastEventPlusPRCL * nominalInterestRate * notionalPrincipal)
        remainingPeriods = ceiling (notionalPrincipal / redemptionPerCycle) - 1
        m = lastEvent <+> principalRedemptionCycle {n = n principalRedemptionCycle * remainingPeriods}
     in eomc scheduleConfig >>= \d -> return $ applyEOMC lastEvent principalRedemptionCycle d m
maturity
  ContractTerms
    { contractType = ANN,
      ct_AD = Nothing,
      ct_MD = Nothing,
      ct_PRANX = Just principalRedemptionAnchor,
      ct_PRNXT = Just nextPrincipalRedemptionPayment,
      ct_IED = Just initialExchangeDate,
      ct_PRCL = Just principalRedemptionCycle,
      ct_NT = Just notionalPrincipal,
      ct_IPNR = Just nominalInterestRate,
      ct_DCC = Just dayCountConvention,
      ct_SD = t0,
      scfg = scheduleConfig
    } =
    let tplus = initialExchangeDate <+> principalRedemptionCycle
        lastEvent
          | principalRedemptionAnchor >= t0 = principalRedemptionAnchor
          | tplus >= t0 = tplus
          | otherwise =
            let previousEvents = generateRecurrentScheduleWithCorrections t0 principalRedemptionCycle principalRedemptionAnchor scheduleConfig
             in calculationDay . head . sortOn (Down . calculationDay) . filter (\ShiftedDay {..} -> calculationDay > t0) $ previousEvents
        timeFromLastEventPlusOneCycle = _y dayCountConvention lastEvent (lastEvent <+> principalRedemptionCycle) Nothing
        redemptionPerCycle = nextPrincipalRedemptionPayment - timeFromLastEventPlusOneCycle * nominalInterestRate * notionalPrincipal
        remainingPeriods = (ceiling (notionalPrincipal / redemptionPerCycle) - 1) :: Integer
    in Just . calculationDay . applyBDCWithCfg scheduleConfig $ lastEvent <+> principalRedemptionCycle { n = remainingPeriods }
maturity
  ContractTerms
    { contractType = ANN,
      ct_AD = ad@(Just _)
    } = ad
maturity
  ContractTerms
    { contractType = ANN,
      ct_AD = Nothing,
      ct_MD = md@(Just _)
    } = md
maturity _ = Nothing
