{-# LANGUAGE RecordWildCards #-}

{-| = ACTUS contract state initialization per t0

The implementation is a transliteration of the ACTUS specification v1.1
Note: initial states rely also on some schedules (and vice versa)

-}

module Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel
  ( initialize
  , initializeState
  )
where

import           Control.Monad.Reader                                   (Reader, ask)
import           Data.Maybe                                             (fromMaybe)
import           Data.Time.LocalTime                                    (LocalTime)
import           Language.Marlowe.ACTUS.Definitions.ContractState       (ContractState, ContractStatePoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (CT (..), ContractTerms, ContractTermsPoly (..),
                                                                         Cycle (..), FEB (..), IPCB (..), SCEF (..))
import           Language.Marlowe.ACTUS.Model.STF.StateTransition       (CtxSTF (..))
import           Language.Marlowe.ACTUS.Model.Utility.ANN.Annuity       (annuity)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (generateRecurrentScheduleWithCorrections, inf',
                                                                         sup')
import           Language.Marlowe.ACTUS.Ops                             (RoleSignOps (_r), YearFractionOps (_y))

{-# ANN module "HLint: ignore Use camelCase" #-}

initializeState :: Reader (CtxSTF Double LocalTime) ContractState
initializeState = ask >>= \CtxSTF {..} -> return $ initialize contractTerms fpSchedule prSchedule ipSchedule maturity

-- |init initializes the state variables at t0
initialize :: ContractTerms -> [LocalTime] -> [LocalTime] -> [LocalTime] -> Maybe LocalTime -> ContractState
initialize
  ct@ContractTermsPoly
    { ct_PRF = Just prf,
      ct_SD = statusDate
    }
  fpSchedule
  prSchedule
  ipSchedule
  m@(Just mat) =
    ContractStatePoly
      { prnxt = nextPrincipalRedemptionPayment ct {ct_MD = m},
        ipcb = interestPaymentCalculationBase ct {ct_MD = m},
        tmd = mat,
        nt = notionalPrincipal ct,
        ipnr = nominalInterestRate ct,
        ipac = accruedInterest ct,
        feac = feeAccrued ct {ct_MD = m},
        nsc = notionalScaling ct,
        isc = interestScaling ct,
        prf = prf,
        sd = statusDate
      }
    where
      t0 = statusDate

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
          let nt = notionalPrincipal ct
              ipnr = nominalInterestRate ct
           in _y dcc tminus t0 m * nt * ipnr
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
            prDates = prSchedule ++ [mat]
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
initialize _ _ _ _ _ = error "maturity and prf need to be defined in ContractTerms"
