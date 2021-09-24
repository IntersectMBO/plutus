{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.STF.StateTransitionFs
  (
    stateTransition
  , CtxSTF (..)
  )
where

import           Control.Monad.Reader
import           Data.Maybe                                             (fromMaybe, maybeToList)
import           Data.Time                                              (LocalTime)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents      (EventType (..), RiskFactorsMarlowe,
                                                                         RiskFactorsPoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState       (ContractStateMarlowe)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (CT (..), ContractTerms, ContractTermsPoly (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule            (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.MarloweCompat                   (constnt, enum, marloweTime)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule    (maturity)
import           Language.Marlowe.ACTUS.Model.STF.StateTransitionModel
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (inf, sup)
import           Language.Marlowe.ACTUS.Ops                             (YearFractionOps (_y))

data CtxSTF = CtxSTF
  { contractTerms :: ContractTerms
  , fpSchedule    :: [ShiftedDay]
  , prSchedule    :: [ShiftedDay]
  }

stateTransition :: EventType -> RiskFactorsMarlowe -> LocalTime -> LocalTime -> ContractStateMarlowe -> Reader CtxSTF ContractStateMarlowe
stateTransition ev rf t1 t2 st = ask >>= \CtxSTF{..} -> return $ stateTransitionFs' ev rf contractTerms t1 t2 st fpSchedule prSchedule

stateTransitionFs' :: EventType -> RiskFactorsMarlowe -> ContractTerms -> LocalTime -> LocalTime -> ContractStateMarlowe -> [ShiftedDay] -> [ShiftedDay] -> ContractStateMarlowe
stateTransitionFs'
  ev
  RiskFactorsPoly{..}
  ct@ContractTermsPoly
    { ct_NT = Just nt,
      ct_DCC = Just dayCountConvention,
      ct_IPANX = Just ipanx,
      ..
    }
  prevDate
  curDate
  st'
  fpSchedule
  prSchedule
  = stf ct ev st'
    where
      stf :: ContractTerms -> EventType -> ContractStateMarlowe -> ContractStateMarlowe

      stf _ AD st = _STF_AD_PAM st time y_sd_t
      stf ContractTermsPoly {contractType = PAM} IED st = _STF_IED_PAM st time y_ipanx_t nominalInterestRate interestPaymentAnchor ct_CNTRL interestAccrued notionalPrincipal
      stf ContractTermsPoly {contractType = LAM} IED st = _STF_IED_LAM st time y_ipanx_t nominalInterestRate interestPaymentAnchor ct_CNTRL interestAccrued notionalPrincipal interestCalculationBase interestCalculationBaseAmont
      stf ContractTermsPoly {contractType = NAM} IED st = _STF_IED_LAM st time y_ipanx_t nominalInterestRate interestPaymentAnchor ct_CNTRL interestAccrued notionalPrincipal interestCalculationBase interestCalculationBaseAmont
      stf ContractTermsPoly {contractType = ANN} IED st = _STF_IED_LAM st time y_ipanx_t nominalInterestRate interestPaymentAnchor ct_CNTRL interestAccrued notionalPrincipal interestCalculationBase interestCalculationBaseAmont
      stf ContractTermsPoly {contractType = LAM} PR st = _STF_PR_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTermsPoly {contractType = NAM} PR st = _STF_PR_NAM st time pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTermsPoly {contractType = ANN} PR st = _STF_PR_NAM st time pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTermsPoly {contractType = PAM} MD st = _STF_MD_PAM st time
      stf ContractTermsPoly {contractType = LAM} MD st = _STF_MD_LAM st time
      stf ContractTermsPoly {contractType = NAM} MD st = _STF_MD_LAM st time
      stf ContractTermsPoly {contractType = ANN} MD st = _STF_MD_LAM st time
      stf ContractTermsPoly {contractType = PAM} PP st = _STF_PP_PAM st time pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTermsPoly {contractType = LAM} PP st = _STF_PP_LAM st time pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTermsPoly {contractType = NAM} PP st = _STF_PP_LAM st time pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTermsPoly {contractType = ANN} PP st = _STF_PP_LAM st time pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTermsPoly {contractType = PAM} PY st = _STF_PY_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTermsPoly {contractType = LAM} PY st = _STF_PY_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTermsPoly {contractType = NAM} PY st = _STF_PY_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTermsPoly {contractType = ANN} PY st = _STF_PY_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTermsPoly {contractType = PAM} FP st = _STF_FP_PAM st time y_sd_t
      stf ContractTermsPoly {contractType = LAM} FP st = _STF_FP_LAM st time y_sd_t
      stf ContractTermsPoly {contractType = NAM} FP st = _STF_FP_LAM st time y_sd_t
      stf ContractTermsPoly {contractType = ANN} FP st = _STF_FP_LAM st time y_sd_t
      stf ContractTermsPoly {contractType = PAM} PRD st = _STF_PRD_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTermsPoly {contractType = LAM} PRD st = _STF_PRD_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTermsPoly {contractType = NAM} PRD st = _STF_PRD_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTermsPoly {contractType = ANN} PRD st = _STF_PRD_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf _ TD st = _STF_TD_PAM st time
      stf _ IP st = _STF_IP_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTermsPoly {contractType = PAM} IPCI st = _STF_IPCI_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTermsPoly {contractType = LAM} IPCI st = _STF_IPCI_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTermsPoly {contractType = NAM} IPCI st = _STF_IPCI_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTermsPoly {contractType = ANN} IPCI st = _STF_IPCI_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTermsPoly {contractType = LAM} IPCB st = _STF_IPCB_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTermsPoly {contractType = NAM} IPCB st = _STF_IPCB_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTermsPoly {contractType = ANN} IPCB st = _STF_IPCB_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf
        ContractTermsPoly
          { contractType = PAM,
            ct_RRLF = Just rrlf,
            ct_RRLC = Just rrlc,
            ct_RRPC = Just rrpc,
            ct_RRPF = Just rrpf,
            ct_RRMLT = Just rrmlt,
            ct_RRSP = Just rrsp
          }
        RR
        st =
          let rrlf' = constnt rrlf
              rrlc' = constnt rrlc
              rrpc' = constnt rrpc
              rrpf' = constnt rrpf
              rrmlt' = constnt rrmlt
              rrsp' = constnt rrsp
           in _STF_RR_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL rrlf' rrlc' rrpc' rrpf' rrmlt' rrsp' o_rf_RRMO
      stf
        ContractTermsPoly
          { contractType = LAM,
            ct_RRLF = Just rrlf,
            ct_RRLC = Just rrlc,
            ct_RRPC = Just rrpc,
            ct_RRPF = Just rrpf,
            ct_RRMLT = Just rrmlt,
            ct_RRSP = Just rrsp
          }
        RR
        st =
          let rrlf' = constnt rrlf
              rrlc' = constnt rrlc
              rrpc' = constnt rrpc
              rrpf' = constnt rrpf
              rrmlt' = constnt rrmlt
              rrsp' = constnt rrsp
           in _STF_RR_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL rrlf' rrlc' rrpc' rrpf' rrmlt' rrsp' o_rf_RRMO
      stf
        ContractTermsPoly
          { contractType = NAM,
            ct_RRLF = Just rrlf,
            ct_RRLC = Just rrlc,
            ct_RRPC = Just rrpc,
            ct_RRPF = Just rrpf,
            ct_RRMLT = Just rrmlt,
            ct_RRSP = Just rrsp
          }
        RR
        st =
          let rrlf' = constnt rrlf
              rrlc' = constnt rrlc
              rrpc' = constnt rrpc
              rrpf' = constnt rrpf
              rrmlt' = constnt rrmlt
              rrsp' = constnt rrsp
           in _STF_RR_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL rrlf' rrlc' rrpc' rrpf' rrmlt' rrsp' o_rf_RRMO
      stf
        ContractTermsPoly
          { contractType = ANN,
            ct_RRLF = Just rrlf,
            ct_RRLC = Just rrlc,
            ct_RRPC = Just rrpc,
            ct_RRPF = Just rrpf,
            ct_RRMLT = Just rrmlt,
            ct_RRSP = Just rrsp
          }
        RR
        st =
          let rrlf' = constnt rrlf
              rrlc' = constnt rrlc
              rrpc' = constnt rrpc
              rrpf' = constnt rrpf
              rrmlt' = constnt rrmlt
              rrsp' = constnt rrsp
           in _STF_RR_ANN st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL rrlf' rrlc' rrpc' rrpf' rrmlt' rrsp' o_rf_RRMO ti
      stf ContractTermsPoly {contractType = PAM} RRF st = _STF_RRF_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL nextRateReset
      stf ContractTermsPoly {contractType = LAM} RRF st = _STF_RRF_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL nextRateReset
      stf ContractTermsPoly {contractType = NAM} RRF st = _STF_RRF_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL nextRateReset
      stf ContractTermsPoly {contractType = ANN,
          ct_RRNXT = Just rrnxt} RRF st = _STF_RRF_ANN st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL (constnt rrnxt) ti
      stf
        ContractTermsPoly
          { contractType = PAM,
            ct_SCEF = Just scef,
            ct_SCIED = Just scied
          }
        SC
        st = _STF_SC_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL scef o_rf_SCMO (constnt scied)
      stf ContractTermsPoly {contractType = ANN} PRF st = _STF_PRF_ANN st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL nextRateReset y_t ti
      stf ContractTermsPoly {contractType = PAM} CE st = _STF_CE_PAM st time y_sd_t
      stf
        ContractTermsPoly
          { contractType = LAM,
            ct_SCEF = Just scef,
            ct_SCIED = Just scied
          }
        SC
        st = _STF_SC_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL scef o_rf_SCMO (constnt scied)
      stf ContractTermsPoly {contractType = LAM} CE st = _STF_CE_PAM st time y_sd_t
      stf
        ContractTermsPoly
          { contractType = NAM,
            ct_SCEF = Just scef,
            ct_SCIED = Just scied
          }
        SC
        st = _STF_SC_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL scef o_rf_SCMO (constnt scied)
      stf
        ContractTermsPoly
          { contractType = ANN,
            ct_SCEF = Just scef,
            ct_SCIED = Just scied
          }
        SC
        st = _STF_SC_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL scef o_rf_SCMO (constnt scied)

      stf _ CE st = _STF_AD_PAM st time y_sd_t

      stf _ _ st = st

      interestPaymentAnchor = marloweTime <$> Just ipanx
      nominalInterestRate = constnt <$> ct_IPNR
      interestAccrued = constnt <$> ct_IPAC
      notionalPrincipal = constnt nt
      feeBase = enum ct_FEB
      feeRate = constnt (fromMaybe 0.0 ct_FER)

      interestCalculationBase = enum <$> ct_IPCB
      interestCalculationBaseAmont = constnt <$> ct_IPCBA
      nextRateReset = constnt <$> ct_RRNXT

      time = marloweTime curDate

      tfp_minus = maybe curDate calculationDay (sup fpSchedule curDate)
      tfp_plus = maybe curDate calculationDay (inf fpSchedule curDate)
      tpr_plus = maybe curDate calculationDay (inf prSchedule curDate)

      y_tfpminus_t = constnt $ _y dayCountConvention tfp_minus curDate ct_MD
      y_tfpminus_tfpplus = constnt $ _y dayCountConvention tfp_minus tfp_plus ct_MD
      y_ipanx_t = constnt $ _y dayCountConvention ipanx curDate ct_MD
      y_sd_t = constnt $ _y dayCountConvention prevDate curDate ct_MD
      y_t = constnt $ _y dayCountConvention curDate tpr_plus ct_MD

      prDates = map calculationDay prSchedule ++ maybeToList (maturity ct)
      prDatesAfterSd = filter (\d -> d > curDate) prDates
      ti = zipWith (\tn tm -> constnt $ _y dayCountConvention tn tm ct_MD) prDatesAfterSd (tail prDatesAfterSd)

stateTransitionFs' _ _ _ _ _ st _ _  = st
