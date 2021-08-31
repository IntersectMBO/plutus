{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule where

import           Control.Applicative                                        (Alternative ((<|>)))
import           Data.Ord                                                   (Down (..))
import           Data.Sort                                                  (sortOn)
import           Data.Time                                                  (Day)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents          (EventType (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState           (ContractStatePoly (tmd))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms           (CT (..), ContractTerms (..), Cycle (..),
                                                                             DCC, ScheduleConfig)
import           Language.Marlowe.ACTUS.Definitions.Schedule                (ShiftedDay (ShiftedDay, calculationDay, paymentDay),
                                                                             ShiftedSchedule)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (_INIT_LAM, _INIT_NAM)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractScheduleModel
import           Language.Marlowe.ACTUS.Model.Utility.DateShift             (applyBDCWithCfg)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator     (generateRecurrentScheduleWithCorrections,
                                                                             inf, plusCycle, sup)
import           Language.Marlowe.ACTUS.Ops                                 (YearFractionOps (_y))


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
maturity ContractTerms{ contractType = PAM, ..} = ct_MD
maturity ct@ContractTerms{ contractType = LAM, ..} =
  let t0                 = ct_SD
      fpSchedule         = schedule FP ct
      tfp_minus          = maybe t0 calculationDay ((\sc -> sup sc t0) =<< fpSchedule)
      tfp_plus           = maybe t0 calculationDay ((\sc -> inf sc t0) =<< fpSchedule)
      ipSchedule         = schedule IP ct
      tminus             = maybe t0 calculationDay ((\sc -> sup sc t0) =<< ipSchedule)
      prSchedule         = schedule PR ct
      tpr_minus          = maybe t0 calculationDay ((\sc -> sup sc t0) =<< prSchedule)
      in Just $ tmd $ _INIT_LAM ct_SD tminus tpr_minus tfp_minus tfp_plus ct

maturity ct@ContractTerms{ contractType = NAM, ..} =
  let t0                 = ct_SD
      fpSchedule         = schedule FP ct
      tfp_minus          = maybe t0 calculationDay ((\sc -> sup sc t0) =<< fpSchedule)
      tfp_plus           = maybe t0 calculationDay ((\sc -> inf sc t0) =<< fpSchedule)
      ipSchedule         = schedule IP ct
      tminus             = maybe t0 calculationDay ((\sc -> sup sc t0) =<< ipSchedule)
      prSchedule         = schedule PR ct
      tpr_minus          = maybe t0 calculationDay ((\sc -> sup sc t0) =<< prSchedule)
      in Just $ tmd $ _INIT_NAM ct_SD tminus tpr_minus tfp_minus tfp_plus ct

maturity ContractTerms{ contractType = ANN, ..} = maturity' ct_SD ct_SD ct_DCC ct_AD ct_MD ct_IED ct_PRANX ct_PRCL ct_PRNXT ct_IPNR ct_NT
  where
    maturity' :: Day            -- t0
              -> Day            -- status date
              -> Maybe DCC      -- day count convention
              -> Maybe Day      -- amorization date
              -> Maybe Day      -- maturity date
              -> Maybe Day      -- initial exchange date
              -> Maybe Day      -- cycle anchor date of principal redemption
              -> Maybe Cycle    -- cycle of principal redemption
              -> Maybe Double   -- next principal redemption payment
              -> Maybe Double   -- nominal interest rate
              -> Maybe Double   -- notional principal
              -> Maybe Day      -- maturity

    maturity' t0 sd (Just dcc) Nothing Nothing (Just ied) (Just pranx) (Just prcl) (Just prnxt) (Just ipnr) (Just nt) =
      let tplus = ied `plusCycle` prcl

          lastEvent
            | pranx >= t0 = pranx
            | tplus >= t0 = tplus
            | otherwise =
              let previousEvents = _S sd prcl pranx scfg
               in calculationDay . head . sortOn (Down . calculationDay) . filter (\ShiftedDay {..} -> calculationDay > t0) $ previousEvents

          timeFromLastEventPlusOneCycle = _y dcc lastEvent (lastEvent `plusCycle` prcl) Nothing

          redemptionPerCycle = prnxt - timeFromLastEventPlusOneCycle * ipnr * nt

          remainingPeriods = (ceiling (nt / redemptionPerCycle) - 1) :: Integer

       in Just . calculationDay . applyBDCWithCfg scfg $ lastEvent `plusCycle` prcl {n = remainingPeriods}

      where
        _S :: Day -> Cycle -> Day -> ScheduleConfig -> ShiftedSchedule
        _S = generateRecurrentScheduleWithCorrections

    maturity' _ _ _ ad@(Just _) _ _ _ _ _ _ _        = ad
    maturity' _ _ _ Nothing md@(Just _) _ _ _ _ _ _  = md
    maturity' _ _ _ _ _ _ _ _ _ _ _                  = Nothing
