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
import           Data.Time                                                (LocalTime)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents        (EventType (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms         (CT (..), ContractTerms,
                                                                           ContractTermsPoly (..), Cycle (..),
                                                                           ScheduleConfig (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule              (ShiftedDay (..))
import           Language.Marlowe.ACTUS.Model.SCHED.ContractScheduleModel
import           Language.Marlowe.ACTUS.Model.Utility.DateShift           (applyBDCWithCfg)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator   (applyEOMC,
                                                                           generateRecurrentScheduleWithCorrections,
                                                                           (<+>), (<->))
import           Language.Marlowe.ACTUS.Model.Utility.YearFraction        (yearFraction)
import           Language.Marlowe.ACTUS.Ops                               (YearFractionOps (_y))

schedule :: EventType -> ContractTerms -> [ShiftedDay]
schedule ev c = schedule' ev c { ct_MD = maturity c }
  where

    schedule' :: EventType -> ContractTerms -> [ShiftedDay]
    schedule' IED  ct@ContractTermsPoly{ contractType = PAM } = _SCHED_IED_PAM ct
    schedule' MD   ct@ContractTermsPoly{ contractType = PAM } = _SCHED_MD_PAM ct
    schedule' PP   ct@ContractTermsPoly{ contractType = PAM } = _SCHED_PP_PAM ct
    schedule' PY   ct@ContractTermsPoly{ contractType = PAM } = _SCHED_PY_PAM ct
    schedule' FP   ct@ContractTermsPoly{ contractType = PAM } = _SCHED_FP_PAM ct
    schedule' PRD  ct@ContractTermsPoly{ contractType = PAM } = _SCHED_PRD_PAM ct
    schedule' TD   ct@ContractTermsPoly{ contractType = PAM } = _SCHED_TD_PAM ct
    schedule' IP   ct@ContractTermsPoly{ contractType = PAM } = _SCHED_IP_PAM ct
    schedule' IPCI ct@ContractTermsPoly{ contractType = PAM } = _SCHED_IPCI_PAM ct
    schedule' RR   ct@ContractTermsPoly{ contractType = PAM } = _SCHED_RR_PAM ct
    schedule' RRF  ct@ContractTermsPoly{ contractType = PAM } = _SCHED_RRF_PAM ct
    schedule' SC   ct@ContractTermsPoly{ contractType = PAM } = _SCHED_SC_PAM ct

    schedule' IED  ct@ContractTermsPoly{ contractType = LAM } = _SCHED_IED_PAM ct
    schedule' PR   ct@ContractTermsPoly{ contractType = LAM } = _SCHED_PR_LAM ct
    schedule' MD   ct@ContractTermsPoly{ contractType = LAM } = _SCHED_MD_LAM ct
    schedule' PP   ct@ContractTermsPoly{ contractType = LAM } = _SCHED_PP_PAM ct
    schedule' PY   ct@ContractTermsPoly{ contractType = LAM } = _SCHED_PY_PAM ct
    schedule' FP   ct@ContractTermsPoly{ contractType = LAM } = _SCHED_FP_PAM ct
    schedule' PRD  ct@ContractTermsPoly{ contractType = LAM } = _SCHED_PRD_PAM ct
    schedule' TD   ct@ContractTermsPoly{ contractType = LAM } = _SCHED_TD_PAM ct
    schedule' IP   ct@ContractTermsPoly{ contractType = LAM } = _SCHED_IP_PAM ct
    schedule' IPCI ct@ContractTermsPoly{ contractType = LAM } = _SCHED_IPCI_PAM ct
    schedule' IPCB ct@ContractTermsPoly{ contractType = LAM } = _SCHED_IPCB_LAM ct
    schedule' RR   ct@ContractTermsPoly{ contractType = LAM } = _SCHED_RR_PAM ct
    schedule' RRF  ct@ContractTermsPoly{ contractType = LAM } = _SCHED_RRF_PAM ct
    schedule' SC   ct@ContractTermsPoly{ contractType = LAM } = _SCHED_SC_PAM ct

    schedule' IED  ct@ContractTermsPoly{ contractType = NAM } = _SCHED_IED_PAM ct
    schedule' PR   ct@ContractTermsPoly{ contractType = NAM } = _SCHED_PR_LAM ct
    schedule' MD   ct@ContractTermsPoly{ contractType = NAM } = _SCHED_MD_PAM ct
    schedule' PP   ct@ContractTermsPoly{ contractType = NAM } = _SCHED_PP_PAM ct
    schedule' PY   ct@ContractTermsPoly{ contractType = NAM } = _SCHED_PY_PAM ct
    schedule' FP   ct@ContractTermsPoly{ contractType = NAM } = _SCHED_FP_PAM ct
    schedule' PRD  ct@ContractTermsPoly{ contractType = NAM } = _SCHED_PRD_PAM ct
    schedule' TD   ct@ContractTermsPoly{ contractType = NAM } = _SCHED_TD_PAM ct
    schedule' IP   ct@ContractTermsPoly{ contractType = NAM } = _SCHED_IP_NAM ct
    schedule' IPCI ct@ContractTermsPoly{ contractType = NAM } = _SCHED_IPCI_NAM ct
    schedule' IPCB ct@ContractTermsPoly{ contractType = NAM } = _SCHED_IPCB_LAM ct
    schedule' RR   ct@ContractTermsPoly{ contractType = NAM } = _SCHED_RR_PAM ct
    schedule' RRF  ct@ContractTermsPoly{ contractType = NAM } = _SCHED_RRF_PAM ct
    schedule' SC   ct@ContractTermsPoly{ contractType = NAM } = _SCHED_SC_PAM ct

    schedule' IED  ct@ContractTermsPoly{ contractType = ANN } = _SCHED_IED_PAM ct
    schedule' PR   ct@ContractTermsPoly{ contractType = ANN } = _SCHED_PR_LAM ct
    schedule' MD   ct@ContractTermsPoly{ contractType = ANN } = _SCHED_MD_PAM c { ct_MD = ct_MD c <|> ct_MD ct }
    schedule' PP   ct@ContractTermsPoly{ contractType = ANN } = _SCHED_PP_PAM ct
    schedule' PY   ct@ContractTermsPoly{ contractType = ANN } = _SCHED_PY_PAM ct
    schedule' FP   ct@ContractTermsPoly{ contractType = ANN } = _SCHED_FP_PAM ct
    schedule' PRD  ct@ContractTermsPoly{ contractType = ANN } = _SCHED_PRD_PAM ct
    schedule' TD   ct@ContractTermsPoly{ contractType = ANN } = _SCHED_TD_PAM ct
    schedule' IP   ct@ContractTermsPoly{ contractType = ANN } = _SCHED_IP_NAM c { ct_MD = ct_MD c <|> ct_MD ct }
    schedule' IPCI ct@ContractTermsPoly{ contractType = ANN } = _SCHED_IPCI_PAM ct
    schedule' IPCB ct@ContractTermsPoly{ contractType = ANN } = _SCHED_IPCB_LAM ct
    schedule' RR   ct@ContractTermsPoly{ contractType = ANN } = _SCHED_RR_PAM ct
    schedule' RRF  ct@ContractTermsPoly{ contractType = ANN } = _SCHED_RRF_PAM ct
    schedule' SC   ct@ContractTermsPoly{ contractType = ANN } = _SCHED_SC_PAM ct
    schedule' PRF  ct@ContractTermsPoly{ contractType = ANN } = _SCHED_PRF_ANN ct

    schedule' _ _                                             = []

maturity :: ContractTerms -> Maybe LocalTime
maturity ContractTermsPoly {contractType = PAM, ..} = ct_MD
maturity ContractTermsPoly {contractType = LAM, ct_MD = md@(Just _)} = md
maturity
  ContractTermsPoly
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
maturity ContractTermsPoly {contractType = NAM, ct_MD = md@(Just _)} = md
maturity
  ContractTermsPoly
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
  ContractTermsPoly
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
  ContractTermsPoly
    { contractType = ANN,
      ct_AD = ad@(Just _)
    } = ad
maturity
  ContractTermsPoly
    { contractType = ANN,
      ct_AD = Nothing,
      ct_MD = md@(Just _)
    } = md
maturity _ = Nothing
