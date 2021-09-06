{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.STF.StateTransitionFs (stateTransitionFs) where

import           Data.Maybe                                             (maybeToList)
import           Data.Time                                              (Day)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (CT (..), ContractTerms (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule            (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule    (maturity, schedule)
import           Language.Marlowe.ACTUS.Model.STF.StateTransitionModel
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (inf, sup)
import           Language.Marlowe.ACTUS.Ops                             (YearFractionOps (_y))

import           Language.Marlowe                                       (Contract)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents      (EventType (..), RiskFactorsPoly (..))
import           Language.Marlowe.ACTUS.MarloweCompat                   (ContractStateMarlowe, RiskFactorsMarlowe,
                                                                         constnt, enum, letval, marloweDate,
                                                                         stateTransitionMarlowe)

stateTransitionFs :: EventType -> RiskFactorsMarlowe -> ContractTerms -> Integer -> Day -> Day -> Contract -> Contract
stateTransitionFs
  ev
  RiskFactorsPoly{..}
  ct@ContractTerms
    { ct_NT = Just nt,
      ct_FER = Just fer,
      ct_DCC = Just dayCountConvention,
      ct_IPANX = Just ipanx,
      ..
    }
  t
  prevDate
  curDate
  continue = addComment $ stateTransitionMarlowe ev t continue $ stf ct
    where
      stf :: ContractTerms -> EventType -> ContractStateMarlowe -> ContractStateMarlowe

      stf _ AD st = _STF_AD_PAM st time y_sd_t
      stf ContractTerms {contractType = PAM} IED st = _STF_IED_PAM st time y_ipanx_t nominalInterestRate interestPaymentAnchor ct_CNTRL interestAccrued notionalPrincipal
      stf ContractTerms {contractType = LAM} IED st = _STF_IED_LAM st time y_ipanx_t nominalInterestRate interestPaymentAnchor ct_CNTRL interestAccrued notionalPrincipal interestCalculationBase interestCalculationBaseAmont
      stf ContractTerms {contractType = NAM} IED st = _STF_IED_LAM st time y_ipanx_t nominalInterestRate interestPaymentAnchor ct_CNTRL interestAccrued notionalPrincipal interestCalculationBase interestCalculationBaseAmont
      stf ContractTerms {contractType = ANN} IED st = _STF_IED_LAM st time y_ipanx_t nominalInterestRate interestPaymentAnchor ct_CNTRL interestAccrued notionalPrincipal interestCalculationBase interestCalculationBaseAmont
      stf ContractTerms {contractType = LAM} PR st = _STF_PR_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTerms {contractType = NAM} PR st = _STF_PR_NAM st time pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTerms {contractType = ANN} PR st = _STF_PR_NAM st time pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTerms {contractType = PAM} MD st = _STF_MD_PAM st time
      stf ContractTerms {contractType = LAM} MD st = _STF_MD_LAM st time
      stf ContractTerms {contractType = NAM} MD st = _STF_MD_LAM st time
      stf ContractTerms {contractType = ANN} MD st = _STF_MD_LAM st time
      stf ContractTerms {contractType = PAM} PP st = _STF_PP_PAM st time pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTerms {contractType = LAM} PP st = _STF_PP_LAM st time pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTerms {contractType = NAM} PP st = _STF_PP_LAM st time pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTerms {contractType = ANN} PP st = _STF_PP_LAM st time pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTerms {contractType = PAM} PY st = _STF_PY_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTerms {contractType = LAM} PY st = _STF_PY_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTerms {contractType = NAM} PY st = _STF_PY_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTerms {contractType = ANN} PY st = _STF_PY_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTerms {contractType = PAM} FP st = _STF_FP_PAM st time y_sd_t
      stf ContractTerms {contractType = LAM} FP st = _STF_FP_LAM st time y_sd_t
      stf ContractTerms {contractType = NAM} FP st = _STF_FP_LAM st time y_sd_t
      stf ContractTerms {contractType = ANN} FP st = _STF_FP_LAM st time y_sd_t
      stf ContractTerms {contractType = PAM} PRD st = _STF_PRD_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTerms {contractType = LAM} PRD st = _STF_PRD_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTerms {contractType = NAM} PRD st = _STF_PRD_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTerms {contractType = ANN} PRD st = _STF_PRD_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf _ TD st = _STF_TD_PAM st time
      stf _ IP st = _STF_IP_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTerms {contractType = PAM} IPCI st = _STF_IPCI_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTerms {contractType = LAM} IPCI st = _STF_IPCI_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTerms {contractType = NAM} IPCI st = _STF_IPCI_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTerms {contractType = ANN} IPCI st = _STF_IPCI_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL interestCalculationBase
      stf ContractTerms {contractType = LAM} IPCB st = _STF_IPCB_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTerms {contractType = NAM} IPCB st = _STF_IPCB_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf ContractTerms {contractType = ANN} IPCB st = _STF_IPCB_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL
      stf
        ContractTerms
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
        ContractTerms
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
        ContractTerms
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
        ContractTerms
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
      stf ContractTerms {contractType = PAM} RRF st = _STF_RRF_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL nextRateReset
      stf ContractTerms {contractType = LAM} RRF st = _STF_RRF_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL nextRateReset
      stf ContractTerms {contractType = NAM} RRF st = _STF_RRF_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL nextRateReset
      stf ContractTerms {contractType = ANN,
          ct_RRNXT = Just rrnxt} RRF st = _STF_RRF_ANN st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL (constnt rrnxt) ti
      stf
        ContractTerms
          { contractType = PAM,
            ct_SCEF = Just scef,
            ct_SCIED = Just scied
          }
        SC
        st = _STF_SC_PAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL scef o_rf_SCMO (constnt scied)
      stf ContractTerms {contractType = ANN} PRF st = _STF_PRF_ANN st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL nextRateReset y_t ti
      stf ContractTerms {contractType = PAM} CE st = _STF_CE_PAM st time y_sd_t
      stf
        ContractTerms
          { contractType = LAM,
            ct_SCEF = Just scef,
            ct_SCIED = Just scied
          }
        SC
        st = _STF_SC_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL scef o_rf_SCMO (constnt scied)
      stf ContractTerms {contractType = LAM} CE st = _STF_CE_PAM st time y_sd_t
      stf
        ContractTerms
          { contractType = NAM,
            ct_SCEF = Just scef,
            ct_SCIED = Just scied
          }
        SC
        st = _STF_SC_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL scef o_rf_SCMO (constnt scied)
      stf
        ContractTerms
          { contractType = ANN,
            ct_SCEF = Just scef,
            ct_SCIED = Just scied
          }
        SC
        st = _STF_SC_LAM st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus feeBase feeRate ct_CNTRL scef o_rf_SCMO (constnt scied)

      stf _ CE st = _STF_AD_PAM st time y_sd_t

      stf _ _ st = st

      interestPaymentAnchor = marloweDate <$> Just ipanx
      nominalInterestRate = constnt <$> ct_IPNR
      interestAccrued = constnt <$> ct_IPAC
      notionalPrincipal = constnt nt
      feeBase = enum ct_FEB
      feeRate = constnt fer

      interestCalculationBase = enum <$> ct_IPCB
      interestCalculationBaseAmont = constnt <$> ct_IPCBA
      nextRateReset = constnt <$> ct_RRNXT

      time = marloweDate curDate
      fpSchedule = schedule FP ct
      prSchedule = schedule PR ct

      tfp_minus = maybe curDate calculationDay ((\sc -> sup sc curDate) =<< fpSchedule)
      tfp_plus = maybe curDate calculationDay ((\sc -> inf sc curDate) =<< fpSchedule)
      tpr_plus = maybe curDate calculationDay ((\sc -> inf sc curDate) =<< prSchedule)

      y_tfpminus_t = constnt $ _y dayCountConvention tfp_minus curDate ct_MD
      y_tfpminus_tfpplus = constnt $ _y dayCountConvention tfp_minus tfp_plus ct_MD
      y_ipanx_t = constnt $ _y dayCountConvention ipanx curDate ct_MD
      y_sd_t = constnt $ _y dayCountConvention prevDate curDate ct_MD
      y_t = constnt $ _y dayCountConvention curDate tpr_plus ct_MD

      prDates = maybe [] (map calculationDay) prSchedule ++ maybeToList (maturity ct)
      prDatesAfterSd = filter (\d -> d > curDate) prDates
      ti = zipWith (\tn tm -> constnt $ _y dayCountConvention tn tm ct_MD) prDatesAfterSd (tail prDatesAfterSd)

      addComment cont = case ev of
        IED -> letval "IED" t (constnt 0) cont
        MD  -> letval "MD" t (constnt 0) cont
        IP  -> letval ("IP:" ++ show curDate ++ show prevDate) t (constnt 0) cont
        RR  -> letval ("RR:" ++ show curDate) t (constnt 0) cont
        FP  -> letval ("FP:" ++ show curDate) t (constnt 0) cont
        _   -> cont
stateTransitionFs _ _ _ _ _ _ c = c
