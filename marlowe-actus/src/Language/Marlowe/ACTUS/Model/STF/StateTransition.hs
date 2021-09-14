{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.STF.StateTransition where

import           Data.Maybe                                             (maybeToList)
import           Data.Time                                              (LocalTime)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents      (EventType (..), RiskFactors,
                                                                         RiskFactorsPoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState       (ContractState, ContractStatePoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (CT (..), ContractTerms (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule            (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule    (maturity, schedule)
import           Language.Marlowe.ACTUS.Model.STF.StateTransitionModel
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (inf, sup)
import           Language.Marlowe.ACTUS.Ops                             (YearFractionOps (_y))

stateTransition :: EventType -> RiskFactors -> ContractTerms -> ContractState -> LocalTime -> ContractState
stateTransition
  ev
  RiskFactorsPoly {..}
  ct@ContractTerms
    { ct_DCC = Just dayCountConvention,
      ct_FER = Just feeRate,
      ct_IPANX = ipanx@(Just interestPaymentAnchor),
      ..
    }
  st@ContractStatePoly {..}
  t = stf ev ct
    where
      stf :: EventType -> ContractTerms -> ContractState
      stf AD _ = _STF_AD_PAM st t y_sd_t
      stf
        IED
        ContractTerms
          { contractType = PAM,
            ct_NT = Just notionalPrincipal
          } = _STF_IED_PAM st t y_ipanx_t ct_IPNR ipanx ct_CNTRL ct_IPAC notionalPrincipal
      stf
        IED
        ContractTerms
          { ct_NT = Just notionalPrincipal
          } = _STF_IED_LAM st t y_ipanx_t ct_IPNR ipanx ct_CNTRL ct_IPAC notionalPrincipal ct_IPCB ct_IPCBA
      stf PR ContractTerms {contractType = LAM} = _STF_PR_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf PR ContractTerms {contractType = NAM} = _STF_PR_NAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf PR ContractTerms {contractType = ANN} = _STF_PR_NAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf MD _ = _STF_MD_PAM st t
      stf PP ContractTerms {contractType = PAM} = _STF_PP_PAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PP ContractTerms {contractType = LAM} = _STF_PP_LAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf PP ContractTerms {contractType = NAM} = _STF_PP_LAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf PP ContractTerms {contractType = ANN} = _STF_PP_LAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf PY ContractTerms {contractType = PAM} = _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PY ContractTerms {contractType = LAM} = _STF_PY_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PY ContractTerms {contractType = NAM} = _STF_PY_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PY ContractTerms {contractType = ANN} = _STF_PY_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf FP ContractTerms {contractType = PAM} = _STF_FP_PAM st t y_sd_t
      stf FP ContractTerms {contractType = LAM} = _STF_FP_LAM st t y_sd_t
      stf FP ContractTerms {contractType = NAM} = _STF_FP_LAM st t y_sd_t
      stf FP ContractTerms {contractType = ANN} = _STF_FP_LAM st t y_sd_t
      stf PRD ContractTerms {contractType = PAM} = _STF_PRD_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PRD ContractTerms {contractType = LAM} = _STF_PRD_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PRD ContractTerms {contractType = NAM} = _STF_PRD_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PRD ContractTerms {contractType = ANN} = _STF_PRD_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf TD _ = _STF_TD_PAM st t
      stf IP _ = _STF_IP_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf IPCI ContractTerms {contractType = PAM} = _STF_IPCI_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf IPCI ContractTerms {contractType = LAM} = _STF_IPCI_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf IPCI ContractTerms {contractType = NAM} = _STF_IPCI_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf IPCI ContractTerms {contractType = ANN} = _STF_IPCI_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf IPCB ContractTerms {contractType = LAM} = _STF_IPCB_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf IPCB ContractTerms {contractType = NAM} = _STF_IPCB_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf IPCB ContractTerms {contractType = ANN} = _STF_IPCB_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf
        RR
        ContractTerms
          { contractType = PAM,
            ct_RRLF = Just rrlf,
            ct_RRLC = Just rrlc,
            ct_RRPC = Just rrpc,
            ct_RRPF = Just rrpf,
            ct_RRMLT = Just rrmlt,
            ct_RRSP = Just rrsp
          } = _STF_RR_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL rrlf rrlc rrpc rrpf rrmlt rrsp o_rf_RRMO
      stf
        RR
        ContractTerms
          { contractType = LAM,
            ct_RRLF = Just rrlf,
            ct_RRLC = Just rrlc,
            ct_RRPC = Just rrpc,
            ct_RRPF = Just rrpf,
            ct_RRMLT = Just rrmlt,
            ct_RRSP = Just rrsp
          } = _STF_RR_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL rrlf rrlc rrpc rrpf rrmlt rrsp o_rf_RRMO
      stf
        RR
        ContractTerms
          { contractType = NAM,
            ct_RRLF = Just rrlf,
            ct_RRLC = Just rrlc,
            ct_RRPC = Just rrpc,
            ct_RRPF = Just rrpf,
            ct_RRMLT = Just rrmlt,
            ct_RRSP = Just rrsp
          } = _STF_RR_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL rrlf rrlc rrpc rrpf rrmlt rrsp o_rf_RRMO
      stf
        RR
        ContractTerms
          { contractType = ANN,
            ct_RRLF = Just rrlf,
            ct_RRLC = Just rrlc,
            ct_RRPC = Just rrpc,
            ct_RRPF = Just rrpf,
            ct_RRMLT = Just rrmlt,
            ct_RRSP = Just rrsp
          } = _STF_RR_ANN st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL rrlf rrlc rrpc rrpf rrmlt rrsp o_rf_RRMO ti
      stf RRF ContractTerms {contractType = PAM} = _STF_RRF_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_RRNXT
      stf RRF ContractTerms {contractType = LAM} = _STF_RRF_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_RRNXT
      stf RRF ContractTerms {contractType = NAM} = _STF_RRF_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_RRNXT
      stf
        RRF
        ContractTerms
          { contractType = ANN,
            ct_RRNXT = Just rrnxt
          } = _STF_RRF_ANN st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL rrnxt ti
      stf PRF ContractTerms {contractType = ANN} = _STF_PRF_ANN st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_RRNXT y_t ti
      stf
        SC
        ContractTerms
          { contractType = PAM,
            ct_SCEF = Just scef,
            ct_SCIED = Just scied
          } = _STF_SC_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL scef o_rf_SCMO scied
      stf
        SC
        ContractTerms
          { contractType = LAM,
            ct_SCEF = Just scef,
            ct_SCCDD = Just sccdd
          } = _STF_SC_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL scef o_rf_SCMO sccdd
      stf
        SC
        ContractTerms
          { contractType = NAM,
            ct_SCEF = Just scef,
            ct_SCCDD = Just sccdd
          } = _STF_SC_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL scef o_rf_SCMO sccdd
      stf
        SC
        ContractTerms
          { contractType = ANN,
            ct_SCEF = Just scef,
            ct_SCCDD = Just sccdd
          } = _STF_SC_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL scef o_rf_SCMO sccdd
      stf CE _ = _STF_CE_PAM st t y_sd_t
      stf _ _ = st

      fpSchedule = schedule FP ct
      prSchedule = schedule PR ct

      tfp_minus = maybe t calculationDay ((\sc -> sup sc t) =<< fpSchedule)
      tfp_plus = maybe t calculationDay ((\sc -> inf sc t) =<< fpSchedule)
      tpr_plus = maybe t calculationDay ((\sc -> inf sc t) =<< prSchedule)

      y_sd_t = _y dayCountConvention sd t ct_MD
      y_tfpminus_t = _y dayCountConvention tfp_minus t ct_MD
      y_tfpminus_tfpplus = _y dayCountConvention tfp_minus tfp_plus ct_MD
      y_ipanx_t = _y dayCountConvention interestPaymentAnchor t ct_MD
      y_t = _y dayCountConvention t tpr_plus ct_MD

      prDates = maybe [] (map calculationDay) prSchedule ++ maybeToList (maturity ct)
      prDatesAfterSd = filter (\d -> d > sd) prDates
      ti = zipWith (\tn tm -> _y dayCountConvention tn tm ct_MD) prDatesAfterSd (tail prDatesAfterSd)
stateTransition _ _ _ s _ = s
