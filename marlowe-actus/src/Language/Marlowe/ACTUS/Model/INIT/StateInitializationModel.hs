{-# LANGUAGE RecordWildCards #-}

{-| = ACTUS contract state initialization per t0

The implementation is a transliteration of the ACTUS specification v1.1
Note: initial states rely also on some schedules (and vice versa)

-}

module Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel
  ( initializeState
  )
where

import           Control.Monad.Reader                                   (Reader, reader)
import           Data.Maybe                                             (fromMaybe)
import           Data.Time.LocalTime                                    (LocalTime)
import           Language.Marlowe.ACTUS.Definitions.ContractState       (ContractState, ContractStatePoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (CT (..), ContractTerms, ContractTermsPoly (..),
                                                                         Cycle (..), FEB (..), IPCB (..), PRF,
                                                                         SCEF (..))
import           Language.Marlowe.ACTUS.Model.STF.StateTransition       (CtxSTF (..))
import           Language.Marlowe.ACTUS.Model.Utility.ANN.Annuity       (annuity)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (generateRecurrentScheduleWithCorrections, inf',
                                                                         sup')
import           Language.Marlowe.ACTUS.Ops                             (RoleSignOps (_r), YearFractionOps (_y))

{-# ANN module "HLint: ignore Use camelCase" #-}

-- |'initializeState' initializes the state variables at t0 based on the
-- provided context
initializeState :: Reader (CtxSTF Double LocalTime) ContractState
initializeState = reader initializeState'
  where
    initializeState' :: CtxSTF Double LocalTime -> ContractState
    initializeState' CtxSTF {..} =
      ContractStatePoly
        { prnxt = nextPrincipalRedemptionPayment contractTerms {ct_MD = maturity},
          ipcb = interestPaymentCalculationBase contractTerms {ct_MD = maturity},
          tmd = contractMaturity maturity,
          nt = notionalPrincipal contractTerms,
          ipnr = nominalInterestRate contractTerms,
          ipac = accruedInterest contractTerms,
          feac = feeAccrued contractTerms {ct_MD = maturity},
          nsc = notionalScaling contractTerms,
          isc = interestScaling contractTerms,
          prf = contractPerformance contractTerms,
          sd = t0
        }
      where
        t0 = ct_SD contractTerms

        tfp_minus = fromMaybe t0 (sup' fpSchedule t0)
        tfp_plus = fromMaybe t0 (inf' fpSchedule t0)
        tminus = fromMaybe t0 (sup' ipSchedule t0)

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

        interestScaling :: ContractTerms -> Double
        interestScaling
          ContractTermsPoly
            { ct_SCEF = Just scef,
              ct_SCIP = Just scip
            } | scef_Ixx scef = scip
        interestScaling _ = 1.0

        notionalScaling :: ContractTerms -> Double
        notionalScaling
          ContractTermsPoly
            { ct_SCEF = Just scef,
              ct_SCNT = Just scnt
            } | scef_xNx scef = scnt
        notionalScaling _ = 1.0

        notionalPrincipal :: ContractTerms -> Double
        notionalPrincipal
          ContractTermsPoly
            { ct_IED = Just initialExchangeDate
            } | initialExchangeDate > t0 = 0.0
        notionalPrincipal
          ContractTermsPoly
            { ct_CNTRL = cntrl,
              ct_NT = Just nt
            } = _r cntrl * nt
        notionalPrincipal _ = 0.0

        nominalInterestRate :: ContractTerms -> Double
        nominalInterestRate
          ContractTermsPoly
            { ct_IED = Just initialExchangeDate
            } | initialExchangeDate > t0 = 0.0
        nominalInterestRate
          ContractTermsPoly
            { ct_IPNR = Just ipnr
            } =
            ipnr
        nominalInterestRate _ = 0.0

        accruedInterest :: ContractTerms -> Double
        accruedInterest
          ContractTermsPoly
            { ct_IPNR = Nothing
            } = 0.0
        accruedInterest
          ContractTermsPoly
            { ct_IPAC = Just ipac
            } = ipac
        accruedInterest
          ContractTermsPoly
            { ct_DCC = Just dcc
            } =
            let nt = notionalPrincipal contractTerms
                ipnr = nominalInterestRate contractTerms
             in _y dcc tminus t0 maturity * nt * ipnr
        accruedInterest _ = 0.0

        nextPrincipalRedemptionPayment :: ContractTerms -> Double
        nextPrincipalRedemptionPayment ContractTermsPoly {contractType = PAM} = 0.0
        nextPrincipalRedemptionPayment ContractTermsPoly {ct_PRNXT = Just prnxt} = prnxt
        nextPrincipalRedemptionPayment
          ContractTermsPoly
            { contractType = LAM,
              ct_PRNXT = Nothing,
              ct_MD = Just maturityDate,
              ct_NT = Just nt,
              ct_PRCL = Just principalRedemptionCycle,
              ct_PRANX = Just principalRedemptionAnchor,
              scfg = scheduleConfig
            } = nt / fromIntegral (length $ generateRecurrentScheduleWithCorrections principalRedemptionAnchor (principalRedemptionCycle {includeEndDay = True}) maturityDate scheduleConfig)
        nextPrincipalRedemptionPayment
          ContractTermsPoly
            { contractType = ANN,
              ct_PRNXT = Nothing,
              ct_IPAC = Just interestAccrued,
              ct_MD = md,
              ct_NT = Just nominalPrincipal,
              ct_IPNR = Just ipnr,
              ct_DCC = Just dayCountConvention
            } =
            let scale = nominalPrincipal + interestAccrued
                frac = annuity ipnr ti
             in frac * scale
            where
              prDates = prSchedule ++ [contractMaturity maturity]
              ti = zipWith (\tn tm -> _y dayCountConvention tn tm md) prDates (tail prDates)
        nextPrincipalRedemptionPayment _ = 0.0

        interestPaymentCalculationBase :: ContractTerms -> Double
        interestPaymentCalculationBase
          ContractTermsPoly
            { contractType = LAM,
              ct_IED = Just initialExchangeDate
            } | t0 < initialExchangeDate = 0.0
        interestPaymentCalculationBase
          ContractTermsPoly
            { ct_NT = Just nt,
              ct_IPCB = Just ipcb,
              ct_CNTRL = cntrl
            } | ipcb == IPCB_NT = _r cntrl * nt
        interestPaymentCalculationBase
          ContractTermsPoly
            { ct_IPCBA = Just ipcba,
              ct_CNTRL = cntrl
            } = _r cntrl * ipcba
        interestPaymentCalculationBase _ = 0.0

        feeAccrued :: ContractTerms -> Double
        feeAccrued
          ContractTermsPoly
            { ct_FER = Nothing
            } = 0.0
        feeAccrued
          ContractTermsPoly
            { ct_FEAC = Just feac
            } = feac
        feeAccrued
          ContractTermsPoly
            { ct_FEB = Just FEB_N,
              ct_DCC = Just dayCountConvention,
              ct_FER = Just fer,
              ct_NT = Just nt,
              ct_MD = md
            } = _y dayCountConvention tfp_minus t0 md * nt * fer
        feeAccrued
          ContractTermsPoly
            { ct_DCC = Just dayCountConvention,
              ct_FER = Just fer,
              ct_MD = md
            } = _y dayCountConvention tfp_minus t0 md / _y dayCountConvention tfp_minus tfp_plus md * fer
        feeAccrued _ = 0.0

        contractPerformance :: ContractTerms -> PRF
        contractPerformance ContractTermsPoly {ct_PRF = Just prf} = prf
        contractPerformance _                                     = error "PRF is not set in ContractTerms"

        contractMaturity :: Maybe LocalTime -> LocalTime
        contractMaturity (Just mat) = mat
        contractMaturity _          = error "Maturity is not specified"
