{-# LANGUAGE RecordWildCards #-}

{-| = ACTUS contract state initialization per t0

The implementation is a transliteration of the ACTUS specification v1.1
Note: initial states rely also on some schedules (and vice versa)

-}

module Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel
  ( initialize )
where

import           Data.Maybe                                             (isJust, isNothing, maybeToList)
import           Data.Time                                              (LocalTime)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents
import           Language.Marlowe.ACTUS.Definitions.ContractState       (ContractState, ContractStatePoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (CR, CT (..), ContractTerms (..), Cycle (..),
                                                                         DCC, FEB (..), IPCB (..), SCEF (..),
                                                                         ScheduleConfig)
import           Language.Marlowe.ACTUS.Definitions.Schedule            (ShiftedDay (..), ShiftedSchedule)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule    (maturity, schedule)
import           Language.Marlowe.ACTUS.Model.Utility.ANN.Annuity       (annuity)
import           Language.Marlowe.ACTUS.Model.Utility.ContractRoleSign  (contractRoleSign)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (generateRecurrentScheduleWithCorrections, inf,
                                                                         sup)
import           Language.Marlowe.ACTUS.Model.Utility.YearFraction      (yearFraction)
import           Language.Marlowe.ACTUS.Ops                             (YearFractionOps (_y))

{-# ANN module "HLint: ignore Use camelCase" #-}

-- |init initializes the state variables at t0
initialize :: ContractTerms -> Maybe ContractState
initialize ct@ContractTerms {..} =
  let mat = maturity ct
   in do
        tmd <- mat

        nt <-
          let nt
                | ct_IED > Just t0 = Just 0.0
                | otherwise = (\x -> r ct_CNTRL * x) <$> ct_NT
           in nt

        ipnr <-
          let ipnr
                | ct_IED > Just t0 = Just 0.0
                | otherwise = ct_IPNR
           in ipnr

        ipac <-
          let ipac
                | isNothing ct_IPNR = Just 0.0
                | isJust ct_IPAC = ct_IPAC
                | otherwise = (\d -> y d tminus t0 ct_MD * nt * ipnr) <$> ct_DCC
           in ipac

        feac <- feeAccrued ct { ct_MD = mat }

        nsc <-
          let nsc
                | maybe False scef_xNx ct_SCEF = ct_SCNT
                | otherwise = Just 1.0
           in nsc

        isc <-
          let isc
                | maybe False scef_Ixx ct_SCEF = ct_SCIP
                | otherwise = Just 1.0
           in isc

        prf <- ct_PRF

        let sd = ct_SD

        prnxt <- nextPrincipalRedemptionPayment ct { ct_MD = mat }
        ipcb <- interestPaymentCalculationBase ct { ct_MD = mat }

        return
          ContractStatePoly
            { prnxt = prnxt,
              ipcb = ipcb,
              tmd = tmd,
              nt = nt,
              ipnr = ipnr,
              ipac = ipac,
              feac = feac,
              nsc = nsc,
              isc = isc,
              prf = prf,
              sd = sd
            }
  where
    fpSchedule = schedule FP ct
    ipSchedule = schedule IP ct
    prSchedule = schedule PR ct

    t0 = ct_SD
    tfp_minus = maybe t0 calculationDay (sup fpSchedule t0)
    tfp_plus = maybe t0 calculationDay (inf fpSchedule t0)
    tminus = maybe t0 calculationDay (sup ipSchedule t0)

    r :: CR -> Double
    r = contractRoleSign

    y :: DCC -> LocalTime -> LocalTime -> Maybe LocalTime -> Double
    y = yearFraction

    _S :: LocalTime -> Cycle -> LocalTime -> ScheduleConfig -> ShiftedSchedule
    _S = generateRecurrentScheduleWithCorrections

    scef_xNx :: SCEF -> Bool
    scef_xNx SE_0N0 = True
    scef_xNx SE_0NM = True
    scef_xNx SE_IN0 = True
    scef_xNx SE_INM = True
    scef_xNx _      = False

    scef_Ixx :: SCEF -> Bool
    scef_Ixx SE_IN0 = True
    scef_Ixx SE_INM = True
    scef_Ixx SE_I00 = True
    scef_Ixx SE_I0M = True
    scef_Ixx _      = False

    nextPrincipalRedemptionPayment :: ContractTerms -> Maybe Double
    nextPrincipalRedemptionPayment ContractTerms {contractType = PAM} = Just 0.0
    nextPrincipalRedemptionPayment ContractTerms {ct_PRNXT = prnxt@(Just _)} = prnxt
    nextPrincipalRedemptionPayment
      ContractTerms
        { contractType = LAM,
          ct_PRNXT = Nothing,
          ct_MD = Just maturityDate,
          ct_NT = Just notionalPrincipal,
          ct_PRCL = Just principalRedemptionCycle,
          ct_PRANX = Just principalRedemptionAnchor,
          scfg = scheduleConfig
        } = Just $ notionalPrincipal / fromIntegral (length $ _S principalRedemptionAnchor (principalRedemptionCycle {includeEndDay = True}) maturityDate scheduleConfig)
    nextPrincipalRedemptionPayment
      ContractTerms
        { contractType = ANN,
          ct_PRNXT = Nothing,
          ct_IPAC = Just interestAccrued,
          ct_MD = md,
          ct_NT = Just nominalPrincipal,
          ct_IPNR = Just nominalInterestRate,
          ct_DCC = Just dayCountConvention
        } =
        let scale = nominalPrincipal + interestAccrued
            frac = annuity nominalInterestRate ti
         in Just $ frac * scale
        where
          prDates = map calculationDay prSchedule ++ maybeToList (maturity ct)
          ti = zipWith (\tn tm -> _y dayCountConvention tn tm md) prDates (tail prDates)
    nextPrincipalRedemptionPayment _ = Nothing

    interestPaymentCalculationBase :: ContractTerms -> Maybe Double
    interestPaymentCalculationBase
        ContractTerms
            { contractType = LAM,
              ct_IED = Just initialExchangeDate
            } | t0 < initialExchangeDate = Just 0.0
    interestPaymentCalculationBase
        ContractTerms
            { ct_NT = Just notionalPrincipal,
              ct_IPCB = Just ipcb
            } | ipcb == IPCB_NT = Just $ r ct_CNTRL * notionalPrincipal
    interestPaymentCalculationBase
        ContractTerms
            { ct_IPCBA = Just ipcba
            } = Just $ r ct_CNTRL * ipcba
    interestPaymentCalculationBase _ = Nothing

    feeAccrued :: ContractTerms -> Maybe Double
    feeAccrued
        ContractTerms
            { ct_FER = Nothing
            } = Just 0.0
    feeAccrued
        ContractTerms
            { ct_FEAC = feac@(Just _)
            } = feac
    feeAccrued
        ContractTerms
            { ct_FEB = Just FEB_N,
              ct_DCC = Just dayCountConvention,
              ct_FER = Just fer,
              ct_NT = Just notionalPrincipal
            } = Just $ y dayCountConvention tfp_minus t0 ct_MD * notionalPrincipal * fer
    feeAccrued
        ContractTerms
            { ct_DCC = Just dayCountConvention,
              ct_FER = Just fer
            } = Just $ y dayCountConvention tfp_minus t0 ct_MD / y dayCountConvention tfp_minus tfp_plus ct_MD * fer
    feeAccrued _ = Nothing
