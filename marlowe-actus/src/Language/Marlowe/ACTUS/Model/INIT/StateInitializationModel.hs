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
        { prnxt = nextPrincipalRedemptionPayment contractTerms,
          ipcb = interestPaymentCalculationBase contractTerms,
          tmd = contractMaturity maturity,
          nt = notionalPrincipal contractTerms,
          ipnr = nominalInterestRate contractTerms,
          ipac = interestAccrued contractTerms,
          feac = feeAccrued contractTerms,
          nsc = notionalScaling contractTerms,
          isc = interestScaling contractTerms,
          prf = contractPerformance contractTerms,
          sd = t0
        }
      where
        t0 = ct_SD contractTerms

        tMinusFP = fromMaybe t0 (sup' fpSchedule t0)
        tPlusFP = fromMaybe t0 (inf' fpSchedule t0)
        tMinusIP = fromMaybe t0 (sup' ipSchedule t0)

        scalingEffect_xNx :: SCEF -> Bool
        scalingEffect_xNx SE_0N0 = True
        scalingEffect_xNx SE_0NM = True
        scalingEffect_xNx SE_IN0 = True
        scalingEffect_xNx SE_INM = True
        scalingEffect_xNx _      = False

        scalingEffect_Ixx :: SCEF -> Bool
        scalingEffect_Ixx SE_IN0 = True
        scalingEffect_Ixx SE_INM = True
        scalingEffect_Ixx SE_I00 = True
        scalingEffect_Ixx SE_I0M = True
        scalingEffect_Ixx _      = False

        interestScaling :: ContractTerms -> Double
        interestScaling
          ContractTermsPoly
            { ct_SCEF = Just scef,
              ct_SCIP = Just scip
            } | scalingEffect_Ixx scef = scip
        interestScaling _ = 1.0

        notionalScaling :: ContractTerms -> Double
        notionalScaling
          ContractTermsPoly
            { ct_SCEF = Just scef,
              ct_SCNT = Just scnt
            } | scalingEffect_xNx scef = scnt
        notionalScaling _ = 1.0

        notionalPrincipal :: ContractTerms -> Double
        notionalPrincipal
          ContractTermsPoly
            { ct_IED = Just ied
            } | ied > t0 = 0.0
        notionalPrincipal
          ContractTermsPoly
            { ct_CNTRL = cntrl,
              ct_NT = Just nt
            } = _r cntrl * nt
        notionalPrincipal _ = 0.0

        nominalInterestRate :: ContractTerms -> Double
        nominalInterestRate
          ContractTermsPoly
            { ct_IED = Just ied
            } | ied > t0 = 0.0
        nominalInterestRate
          ContractTermsPoly
            { ct_IPNR = Just ipnr
            } =
            ipnr
        nominalInterestRate _ = 0.0

        interestAccrued :: ContractTerms -> Double
        interestAccrued
          ContractTermsPoly
            { ct_IPNR = Nothing
            } = 0.0
        interestAccrued
          ContractTermsPoly
            { ct_IPAC = Just ipac
            } = ipac
        interestAccrued
          ContractTermsPoly
            { ct_DCC = Just dcc
            } =
            let nt = notionalPrincipal contractTerms
                ipnr = nominalInterestRate contractTerms
             in _y dcc tMinusIP t0 maturity * nt * ipnr
        interestAccrued _ = 0.0

        nextPrincipalRedemptionPayment :: ContractTerms -> Double
        nextPrincipalRedemptionPayment ContractTermsPoly {contractType = PAM} = 0.0
        nextPrincipalRedemptionPayment ContractTermsPoly {ct_PRNXT = Just prnxt} = prnxt
        nextPrincipalRedemptionPayment
          ContractTermsPoly
            { contractType = LAM,
              ct_PRNXT = Nothing,
              ct_MD = Just md,
              ct_NT = Just nt,
              ct_PRCL = Just prcl,
              ct_PRANX = Just pranx,
              scfg = scfg
            } = nt / fromIntegral (length $ generateRecurrentScheduleWithCorrections pranx (prcl {includeEndDay = True}) md scfg)
        nextPrincipalRedemptionPayment
          ContractTermsPoly
            { contractType = ANN,
              ct_PRNXT = Nothing,
              ct_IPAC = Just ipac,
              ct_MD = md,
              ct_NT = Just nt,
              ct_IPNR = Just ipnr,
              ct_DCC = Just dcc
            } =
            let scale = nt + ipac
                frac = annuity ipnr ti
             in frac * scale
            where
              prDates = prSchedule ++ [contractMaturity maturity]
              ti = zipWith (\tn tm -> _y dcc tn tm md) prDates (tail prDates)
        nextPrincipalRedemptionPayment _ = 0.0

        interestPaymentCalculationBase :: ContractTerms -> Double
        interestPaymentCalculationBase
          ContractTermsPoly
            { contractType = LAM,
              ct_IED = Just ied
            } | t0 < ied = 0.0
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
              ct_DCC = Just dcc,
              ct_FER = Just fer,
              ct_NT = Just nt,
              ct_MD = md
            } = _y dcc tMinusFP t0 md * nt * fer
        feeAccrued
          ContractTermsPoly
            { ct_DCC = Just dcc,
              ct_FER = Just fer,
              ct_MD = md
            } = _y dcc tMinusFP t0 md / _y dcc tMinusFP tPlusFP md * fer
        feeAccrued _ = 0.0

        contractPerformance :: ContractTerms -> PRF
        contractPerformance ContractTermsPoly {ct_PRF = Just prf} = prf
        contractPerformance _                                     = error "PRF is not set in ContractTerms"

        contractMaturity :: Maybe LocalTime -> LocalTime
        contractMaturity (Just mat) = mat
        contractMaturity _          = error "Maturity is not specified"
